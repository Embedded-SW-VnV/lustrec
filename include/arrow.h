#ifndef _ARROW
#define _ARROW

struct _arrow_mem {
  struct _arrow_reg {_Bool _first; } _reg;
};

extern struct _arrow_mem *_arrow_alloc ();

extern void _arrow_dealloc (struct _arrow_mem *);

#define _arrow_DECLARE(attr, inst)\
  attr struct _arrow_mem inst;
  
#define _arrow_LINK(inst) do {\
  ;\
} while (0)

#define _arrow_ALLOC(attr, inst)\
  _arrow_DECLARE(attr, inst);\
  _arrow_LINK(inst)

#define _arrow_init(self) {}

#define _arrow_clear(self) {}

#define _arrow_reset(self) {(self)->_reg._first = 1;}

_Bool _arrow_step(struct _arrow_mem *self);

#endif
