#include "oct_internal.h"

void startfuncdebug(const char *fname) {
  fprintf(stderr, "start function: %s\n", fname);
}
  
void endfuncdebug(const char *fname) {
  //fprintf(stderr, "end function: %s\n", fname);
}
  
