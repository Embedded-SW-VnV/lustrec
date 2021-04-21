#ifndef ARROW_SPEC_H_
#define ARROW_SPEC_H_

/* ACSL arrow spec */
//@ ghost struct _arrow_mem_ghost {struct _arrow_reg _reg;};
/*@
   predicate _arrow_valid(struct _arrow_mem *self) =
     \valid(self);
*/
/*@
   predicate _arrow_initialization(struct _arrow_mem_ghost mem_in) =
     mem_in._reg._first == 1;
*/
/*@
   predicate _arrow_transition(struct _arrow_mem_ghost mem_in,
                               integer x, integer y,
                               struct _arrow_mem_ghost mem_out, _Bool out) =
     (mem_in._reg._first ? (mem_out._reg._first == 0
                            && out == x)
                         : (mem_out._reg._first == mem_in._reg._first
                            && out == y));
*/
/*@
   predicate _arrow_ghost(struct _arrow_mem_ghost mem,
                          struct _arrow_mem *self) =
     mem._reg._first == self->_reg._first;
*/

#endif // ARROW_SPEC_H_
