#if defined(__CYGWIN__) || defined(_WIN32)
#define __WINDOWS__
#else
#include <sys/resource.h>
#endif

#include <caml/config.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>

/* time is a record
  { total : float;
    user : float;
    system : float }
*/

CAMLprim value get_resources(value time)
{
  CAMLparam1(time);
  CAMLlocal1(result);
#ifdef __WINDOWS__
  result = Val_long(-1);
#else
  long unit_mem;
  /* MacOS measures maxrss in bytes, Linux measures it in kilobytes */
  #ifdef __APPLE__
    unit_mem = 1024;
  #else
    unit_mem = 1;
  #endif
  struct rusage rusage;
  double user, system;
  getrusage(RUSAGE_CHILDREN, &rusage);
  user = rusage.ru_utime.tv_sec + rusage.ru_utime.tv_usec * 1e-6;
  system = rusage.ru_stime.tv_sec + rusage.ru_stime.tv_usec * 1e-6;
  Store_double_field(time, 0, user + system);
  Store_double_field(time, 1, user);
  Store_double_field(time, 2, system);
  result = Val_long(rusage.ru_maxrss / unit_mem);
#endif
  CAMLreturn(result);
}
