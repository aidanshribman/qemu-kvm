/*
 * QEMU live migration
 *
 * Copyright IBM, Corp. 2008
 *
 * Authors:
 *  Anthony Liguori   <aliguori@us.ibm.com>
 *
 * This work is licensed under the terms of the GNU GPL, version 2.  See
 * the COPYING file in the top-level directory.
 *
 */

#include "qemu-common.h"
#include "migration.h"
#include "monitor.h"
#include "buffered_file.h"
#include "sysemu.h"
#include "block.h"
#include "qemu_socket.h"

//#define DEBUG_MIGRATION

#ifdef DEBUG_MIGRATION
#define dprintf(fmt, ...) \
    do { printf("migration: " fmt, ## __VA_ARGS__); } while (0)
#else
#define dprintf(fmt, ...) \
    do { } while (0)
#endif

#ifdef SAP_XBRLE
int mig_compression_type = 0;
uint32_t mig_cache_size = 0;
static int is_mig_warmup = 0;
#endif /* SAP_XBRLE */

/* Migration speed throttling */
static uint32_t max_throttle = (32 << 20);

static MigrationState *current_migration;

void qemu_start_incoming_migration(const char *uri)
{
    const char *p;

    if (strstart(uri, "tcp:", &p))
        tcp_start_incoming_migration(p);
#if !defined(WIN32)
    else if (strstart(uri, "exec:", &p))
        exec_start_incoming_migration(p);
    else if (strstart(uri, "unix:", &p))
        unix_start_incoming_migration(p);
    else if (strstart(uri, "fd:", &p))
        fd_start_incoming_migration(p);
#endif
    else
        fprintf(stderr, "unknown migration protocol: %s\n", uri);
}

void do_migrate(Monitor *mon, const QDict *qdict)
{
    MigrationState *s = NULL;
    const char *p;
    int detach = qdict_get_int(qdict, "detach");
    const char *uri = qdict_get_str(qdict, "uri");

    if (strstart(uri, "tcp:", &p))
        s = tcp_start_outgoing_migration(p, max_throttle, detach);
#if !defined(WIN32)
    else if (strstart(uri, "exec:", &p))
        s = exec_start_outgoing_migration(p, max_throttle, detach);
    else if (strstart(uri, "unix:", &p))
        s = unix_start_outgoing_migration(p, max_throttle, detach);
    else if (strstart(uri, "fd:", &p))
        s = fd_start_outgoing_migration(mon, p, max_throttle, detach);
#endif
    else
        monitor_printf(mon, "unknown migration protocol: %s\n", uri);

    if (s == NULL)
        monitor_printf(mon, "migration failed\n");
    else {
        if (current_migration)
            current_migration->release(current_migration);

        current_migration = s;
    }
}

void do_migrate_cancel(Monitor *mon, const QDict *qdict)
{
    MigrationState *s = current_migration;

    if (s)
        s->cancel(s);
}

void do_migrate_set_speed(Monitor *mon, const QDict *qdict)
{
    double d;
    char *ptr;
    FdMigrationState *s;
    const char *value = qdict_get_str(qdict, "value");

    d = strtod(value, &ptr);
    switch (*ptr) {
    case 'G': case 'g':
        d *= 1024;
    case 'M': case 'm':
        d *= 1024;
    case 'K': case 'k':
        d *= 1024;
    default:
        break;
    }

    max_throttle = (uint32_t)d;
    s = migrate_to_fms(current_migration);

    if (s) {
        qemu_file_set_rate_limit(s->file, max_throttle);
    }
    
}

/* amount of nanoseconds we are willing to wait for migration to be down.
 * the choice of nanoseconds is because it is the maximum resolution that
 * get_clock() can achieve. It is an internal measure. All user-visible
 * units must be in seconds */
static uint64_t max_downtime = 50;

uint64_t migrate_max_downtime(void)
{
    return max_downtime;
}

void do_migrate_set_downtime(Monitor *mon, const QDict *qdict)
{
    char *ptr;
    double d;
    const char *value = qdict_get_str(qdict, "value");

    d = strtod(value, &ptr);
    if (!strcmp(ptr,"ms")) {
        d *= 1000000;
    } else if (!strcmp(ptr,"us")) {
        d *= 1000;
    } else if (!strcmp(ptr,"ns")) {
    } else {
        /* all else considered to be seconds */
        d *= 1000000000;
    }

    max_downtime = (uint64_t)d;
}

void do_migrate_set_compression(Monitor *mon, const QDict *qdict)
{
    const char *value = qdict_get_str(qdict, "value");

    if (!strcmp(value,"none")) {
        mig_compression_type = COMP_NONE;
    } else if (!strcmp(value,"xbrle")) {
        mig_compression_type = COMP_XBRLE;
    }
}

void do_info_migrate(Monitor *mon)
{
    MigrationState *s = current_migration;

    if (s) {
        monitor_printf(mon, "Migration status: ");
        switch (s->get_status(s)) {
        case MIG_STATE_ACTIVE:
            monitor_printf(mon, "active\n");
            monitor_printf(mon, "transferred ram: %" PRIu64 " kbytes\n", ram_bytes_transferred() >> 10);
            monitor_printf(mon, "remaining ram: %" PRIu64 " kbytes\n", ram_bytes_remaining() >> 10);
            monitor_printf(mon, "total ram: %" PRIu64 " kbytes\n", ram_bytes_total() >> 10);
            break;
        case MIG_STATE_COMPLETED:
            monitor_printf(mon, "completed\n");
            break;
        case MIG_STATE_ERROR:
            monitor_printf(mon, "failed\n");
            break;
        case MIG_STATE_CANCELLED:
            monitor_printf(mon, "cancelled\n");
            break;
        }
    }
}

/* shared migration helpers */

void migrate_fd_monitor_suspend(FdMigrationState *s)
{
    s->mon_resume = cur_mon;
    if (monitor_suspend(cur_mon) == 0) {
        dprintf("suspending monitor\n");
    } else {
        monitor_printf(cur_mon, "terminal does not allow synchronous "
                       "migration, continuing detached\n");
    }
}

void migrate_fd_error(FdMigrationState *s)
{
    dprintf("setting error state\n");
    s->state = MIG_STATE_ERROR;
    migrate_fd_cleanup(s);
}

void migrate_fd_cleanup(FdMigrationState *s)
{
    qemu_set_fd_handler2(s->fd, NULL, NULL, NULL, NULL);

    if (s->file) {
        dprintf("closing file\n");
        qemu_fclose(s->file);
    }

    if (s->fd != -1)
        close(s->fd);

    /* Don't resume monitor until we've flushed all of the buffers */
    if (s->mon_resume)
        monitor_resume(s->mon_resume);

    s->fd = -1;
}

void migrate_fd_put_notify(void *opaque)
{
    FdMigrationState *s = opaque;

    qemu_set_fd_handler2(s->fd, NULL, NULL, NULL, NULL);
    qemu_file_put_notify(s->file);
}

ssize_t migrate_fd_put_buffer(void *opaque, const void *data, size_t size)
{
    FdMigrationState *s = opaque;
    ssize_t ret;

    do {
        ret = s->write(s, data, size);
    } while (ret == -1 && ((s->get_error(s)) == EINTR));

    if (ret == -1)
        ret = -(s->get_error(s));

    if (ret == -EAGAIN)
        qemu_set_fd_handler2(s->fd, NULL, NULL, migrate_fd_put_notify, s);

    return ret;
}

void migrate_fd_connect(FdMigrationState *s)
{
    int ret;

    s->file = qemu_fopen_ops_buffered(s,
                                      s->bandwidth_limit,
                                      migrate_fd_put_buffer,
                                      migrate_fd_put_ready,
                                      migrate_fd_wait_for_unfreeze,
                                      migrate_fd_close);

    dprintf("beginning savevm\n");
    ret = qemu_savevm_state_begin(s->file);
    if (ret < 0) {
        dprintf("failed, %d\n", ret);
        migrate_fd_error(s);
        return;
    }

    migrate_fd_put_ready(s);
}

void migrate_fd_put_ready(void *opaque)
{
    FdMigrationState *s = opaque;

    if (s->state != MIG_STATE_ACTIVE) {
        dprintf("put_ready returning because of non-active state\n");
        return;
    }

    dprintf("iterate\n");
#ifdef SAP_XBRLE
    if (is_mig_warmup)
	    qemu_savevm_state_warmup(s->file);
    else
#endif /* SAP_XBRLE */
    if (qemu_savevm_state_iterate(s->file) == 1) {
        int state;
        int old_vm_running = vm_running;

        dprintf("done iterating\n");
        vm_stop(0);

        qemu_aio_flush();
        bdrv_flush_all();
        if ((qemu_savevm_state_complete(s->file)) < 0) {
            if (old_vm_running) {
                vm_start();
            }
            state = MIG_STATE_ERROR;
        } else {
            state = MIG_STATE_COMPLETED;
        }
        migrate_fd_cleanup(s);
        s->state = state;
    }
}

int migrate_fd_get_status(MigrationState *mig_state)
{
    FdMigrationState *s = migrate_to_fms(mig_state);
    return s->state;
}

void migrate_fd_cancel(MigrationState *mig_state)
{
    FdMigrationState *s = migrate_to_fms(mig_state);

    if (s->state != MIG_STATE_ACTIVE)
        return;

    dprintf("cancelling migration\n");

    s->state = MIG_STATE_CANCELLED;

    migrate_fd_cleanup(s);
}

void migrate_fd_release(MigrationState *mig_state)
{
    FdMigrationState *s = migrate_to_fms(mig_state);

    dprintf("releasing state\n");
   
    if (s->state == MIG_STATE_ACTIVE) {
        s->state = MIG_STATE_CANCELLED;
        migrate_fd_cleanup(s);
    }
    free(s);
}

void migrate_fd_wait_for_unfreeze(void *opaque)
{
    FdMigrationState *s = opaque;
    int ret;

    dprintf("wait for unfreeze\n");
    if (s->state != MIG_STATE_ACTIVE)
        return;

    do {
        fd_set wfds;

        FD_ZERO(&wfds);
        FD_SET(s->fd, &wfds);

        ret = select(s->fd + 1, NULL, &wfds, NULL, NULL);
    } while (ret == -1 && (s->get_error(s)) == EINTR);
}

int migrate_fd_close(void *opaque)
{
    FdMigrationState *s = opaque;

    qemu_set_fd_handler2(s->fd, NULL, NULL, NULL, NULL);
    return s->close(s);
}

#ifdef SAP_XBRLE
void do_migrate_warmup(Monitor *mon, const QDict *qdict)
{
	if (!vm_running)
		return;
	if (is_mig_warmup)
		return;

	monitor_printf(mon, "Warmup is enabled!\n");
	do_migrate(mon,qdict);
	is_mig_warmup = 1;
}

void do_migrate_warmup_full(Monitor *mon, const QDict *qdict)
{
	if (!vm_running)
		return;
	if (!is_mig_warmup)
		return;
	monitor_printf(mon, "Switching to full live migration!\n");
	is_mig_warmup = 0;
}

void do_migrate_set_cachesize(Monitor *mon, const QDict *qdict)
{
    double d;
    char *ptr;
    const char *value = qdict_get_str(qdict, "value");

    d = strtod(value, &ptr);
    switch (*ptr) {
    case 'G': case 'g':
        d *= 1024;
    case 'M': case 'm':
        d *= 1024;
    case 'K': case 'k':
        d *= 1024;
    default:
        break;
    }

    mig_cache_size = (uint32_t)d;
    monitor_printf(mon, "Cache size set to: %d\n", (uint32_t)d);
}
#endif /* SAP_XBRLE */
