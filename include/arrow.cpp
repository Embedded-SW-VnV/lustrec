#include <stdlib.h>
#include "arrow.hpp"

struct _arrow_mem *_arrow_alloc() {
  struct _arrow_mem *_alloc;
  _alloc = (struct _arrow_mem *) malloc(sizeof(struct _arrow_mem *));
  assert (_alloc);
  return _alloc;
}
