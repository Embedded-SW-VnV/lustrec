#ifndef ARROW_SPEC_H_
#define ARROW_SPEC_H_

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

/* ACSL arrow spec */
//@ ghost struct _arrow_mem_ghost {struct _arrow_reg _reg;};

#define _arrow_reset_ghost(mem) (mem)._reg._first = 1
#define _arrow_step_ghost(mem) (mem)._reg._first = 0

/*@ predicate _arrow_initialization(struct _arrow_mem_ghost mem_in) =
      mem_in._reg._first == 1;
 */

/*@ predicate _arrow_transition(struct _arrow_mem_ghost mem_in,
                                _Bool out,
                                struct _arrow_mem_ghost mem_out) =
      out == mem_in._reg._first
      && (mem_in._reg._first ? (mem_out._reg._first == 0)
                             : (mem_out._reg._first == mem_in._reg._first));
*/

/*@ predicate _arrow_pack(struct _arrow_mem_ghost mem,
                          struct _arrow_mem *self) =
      mem._reg._first == self->_reg._first;
*/

/*@
  requires \separated(mem, self);
  requires _arrow_pack(*mem, self);
  ensures  _arrow_pack(*mem, self);
  ensures \result == \old(self->_reg._first);
  ensures self->_reg._first == 0;
  ensures !\old(mem->_reg._first) ==> *mem == \old(*mem);
  assigns mem->_reg._first, self->_reg._first;
*/
_Bool _arrow_step(struct _arrow_mem *self)
       /*@ ghost (struct _arrow_mem_ghost \ghost *mem) */;

#endif // ARROW_SPEC_H_
