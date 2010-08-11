#ifdef SAP_XBRLE
#include "qemu-common.h"

/* prints a timestamped to stderr */
void stderr_puttimestamp(void)
{
	struct tm *Tm;
	    struct timeval detail_time;
	    int ms;
	    time_t ltime;

	    //get time
	    gettimeofday(&detail_time,NULL);
	    ltime=time(NULL);
	    Tm=localtime(&ltime);
	    //get milliseconds
	    ms = detail_time.tv_usec /1000;

	    //format as: (date time ms) -
	    fprintf(stderr,"(%d-%d-%d %d:%02d:%02d.%03d) - ",
	         Tm->tm_mday,
	         Tm->tm_mon+1,
	         Tm->tm_year+1900,
	         Tm->tm_hour,
	         Tm->tm_min,
	         Tm->tm_sec,ms);
}

/* prints a timestamped message to stderr */
void stderr_puts_timestamp(const char *s)
{
	stderr_puttimestamp();
	fprintf(stderr,"%s",s);
}

/* prints a message to stderr */
void stderr_puts(const char *s)
{
	fprintf(stderr,"%s",s);
}

/* prints an int to stderr */
void stderr_puti(int i)
{
    fprintf(stderr,"%d", i);
}

#endif /* SAP_XBRLE */

