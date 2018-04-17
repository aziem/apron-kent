#include "oct.h"
#include "oct_internal.h"
#include "seqalgorithms.h" 

bool incrclosure_seq(dbm* m, size_t dim, size_t a, size_t b, bound_t d) {
  /* fprintf(stderr, "incremental_closure\n"); */
  size_t i,j;
  size_t bara = a^1;
  size_t barb = b^1;


  // redundancy check
  if (bound_cmp(d, *getdbm(m,matpos2(a,b))) >= 0) {
    return false;
  }

  // sat check
  // m_{b,a} + d < 0
  // m_{bara, barb} < 0 (no need by coherence)
  // m_{bara,a} + d + m_{b,barb} + d < 0

  bound_t temp1; bound_init(temp1);
  bound_t temp2; bound_init(temp2);

  bound_add(temp1, *getdbm(m,matpos2(b,a)), d);
  bound_add(temp2, *getdbm(m,matpos2(bara,a)), d);
  bound_badd(temp2, *getdbm(m,matpos2(b,barb)));
  bound_badd(temp2, d);
  
  if ((bound_sgn(temp1) < 0) || (bound_sgn(temp2) < 0)) {
    bound_clear(temp1);
    bound_clear(temp2);
    return true;
  }

  bound_t twod; bound_init(twod);
  bound_mul_2(twod, d);
 
  bound_add(temp1, twod, *getdbm(m,matpos2(bara,a)));
  bound_add(temp2, twod, *getdbm(m,matpos2(b,barb)));

  /* fprintf(stderr, "m_baraa is infinity: %d\n", is_my_infty(m, matpos2(bara,a))); */
  /* fprintf(stderr, "m_bbarb is infinity: %d\n", is_my_infty(m, matpos2(b,barb))); */
  /* fprintf(stderr, "d is infinity: %d\n", bound_infty(d)); */

  size_t sz_mat = matsize(dim);

  // No need to call strong closure here - inlined into single seq helper

#if defined(STRONGINCR)
  strong_helper(m,dim,a,b,d,temp1,temp2);
#endif

  single_seq_helper(m, m, dim, 0, sz_mat, a, b, d, temp1, temp2);
/* #if defined(FLOYDOPT) */
/*   single_seq_helper(m, m, dim, 0, sz_mat, a, b, d, temp1, temp2); */
/* #endif */

  bound_clear(temp1);
  bound_clear(temp2);
  bound_clear(twod);

#if defined(STRONGINCR)
  return false;
#else
  return hmat_s_step(m,dim);
#endif
}

