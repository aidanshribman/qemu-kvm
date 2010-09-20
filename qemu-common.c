#ifdef SAP_XBRLE
#include <stdio.h>
#include <stdlib.h>
#include "qemu-common.h"

/* prints a timestamped to stderr */
void fprint_timestamp(FILE *fp)
{
    struct tm *Tm;
    struct timeval detail_time;
    int ms;
    time_t ltime;

    /* get time */
    gettimeofday(&detail_time,NULL);
    ltime=time(NULL);
    Tm=localtime(&ltime);

    /* get milliseconds */
    ms = detail_time.tv_usec /1000;

    /* format as: (date time ms) */
    fprintf(fp, "(%d-%d-%d %d:%02d:%02d.%03d) - ",
	    Tm->tm_mday, Tm->tm_mon+1, Tm->tm_year+1900,
	    Tm->tm_hour, Tm->tm_min, Tm->tm_sec,ms);
}
#endif /* SAP_XBRLE */

