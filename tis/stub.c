
int rand(void) {
  return 137;
}

#ifdef __TIS_USER_OPEN

#include <stdarg.h>
#include <assert.h>

int open(const char * filename, int flags, ...) {
  va_list va;
  va_start(va, flags);
  int rv = __mkfs_open(filename, flags, va);
  //@ assert UB: rv >= 0;
  va_end(va);
  return rv;
}

#endif // __TIS_USER_OPEN
