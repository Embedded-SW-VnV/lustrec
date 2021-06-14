#include <stdlib.h>
#include <assert.h>
#include "arrow_spec.h"

struct _arrow_mem * _arrow_alloc () {
  struct _arrow_mem *_alloc;
  _alloc = (struct _arrow_mem *) malloc(sizeof(struct _arrow_mem *));
  assert (_alloc);
  return _alloc;
}

void _arrow_dealloc (struct _arrow_mem * _alloc) {
  free (_alloc);
}

_Bool _arrow_step(struct _arrow_mem *self)
       /*@ ghost (struct _arrow_mem_ghost \ghost *mem) */
{
  if (self->_reg._first) {
    self->_reg._first = 0;
    //@ ghost _arrow_step_ghost(*mem);
    return 1;
  }
  return 0;
}
