#include <stdlib.h>
#include <assert.h>
#include "arrow.hpp"

struct _arrow_mem *_arrow_alloc() {
  struct _arrow_mem *_alloc;
  _alloc = (struct _arrow_mem *) malloc(sizeof(struct _arrow_mem *));
  assert (_alloc);
  return _alloc;
}

void _arrow_dealloc (struct _arrow_mem * _alloc) {
  free (_alloc);
}

bool _arrow_step(struct _arrow_mem *self) {
  if (self->_reg._first) {
    self->_reg._first = 0;
    return 1;
  }
  return 0;
}



