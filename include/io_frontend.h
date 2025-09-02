#ifndef _IO_FRONTEND
#define _IO_FRONTEND

/* Print a prompt ? ************************/
extern int ISATTY;

/* Standard Input procedures **************/

/*@ assigns *n; */
extern _Bool _get_bool(const char* n);

/*@ assigns *n; */
extern int _get_int(const char* n);

/*@ assigns *n; */
extern double _get_double(const char* n);

/* Standard Output procedures **************/
/*@ assigns \nothing; */
extern void _put_bool(const char* n, _Bool _V);

/*@ assigns \nothing; */
extern void _put_int(const char* n, int _V);

/*@ assigns \nothing; */
extern void _put_float(const char* n, float _V, int PREC);

/*@ assigns \nothing; */
extern void _put_double(const char* n, double _V, int PREC);

#endif
