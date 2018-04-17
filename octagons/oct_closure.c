/*
 * oct_closure.c
 *
 * Half-matrices - Closure algorithms
 *
 * APRON Library / Octagonal Domain
 *
 * Copyright (C) Antoine Mine' 2006
 *
 */

/* This file is part of the APRON Library, released under LGPL license
   with an exception allowing the redistribution of statically linked
   executables.

   Please read the COPYING file packaged in the distribution.
*/

#include "oct.h"
#include "oct_internal.h"
#include "incr_closure_seq.h"

/* All closures are in-place. */


/* ============================================================ */
/* Full Closure */
/* ============================================================ */


/* unary constraint propagation */
bool hmat_s_step(dbm* m, size_t dim)
{
  size_t i,j,k;
  bound_t ik,ij;

  bound_init(ik); bound_init(ij);

  /* lone S step */
  for (i=0;i<2*dim;i++) {
    bound_div_2(ij,*getdbm(m,matpos(i,i^1)));
    for (j=0;j<=(i|1);j++) {
      bound_div_2(ik,*getdbm(m,matpos(j^1,j)));
      bound_badd(ik,ij);
      setdbmbmin(m,matpos2(i,j),ik);
    }
  }

  bound_clear(ik); bound_clear(ij);
  /* emptyness checking */
  for (i=0;i<2*dim;i++) {
    if (bound_sgn(*getdbm(m,matpos(i,i)))<0) return true;
    setdbmzero(m,matpos(i,i));
  }

  return false;
}

/* We use a variant of Floyd-Warshall shortest-path closure algorithm, with
   some extra constraint propagation step.
   

   Returns true if the resulting matrix is empty, false otherwise
   (does not free the matrix)

   Cubic time. Constant space.
 */


bool hmat_close(oct_internal_t* pr, dbm* m, size_t dim)
{
  size_t i,j,k;
  bound_t *c,ik,ik2,ij;

  bound_init(ik); bound_init(ik2); bound_init(ij);
#if defined(FLOYDOPT)
  short mik_index, mik2_index;
  short mkj_index, mk2j_index;
#endif

  /* Floyd-Warshall */
  for (k=0;k<2*dim;k++) {
    size_t k2 = k^1;
    //c = m;
    for (i=0;i<2*dim;i++) {
      size_t i2 = i|1;
      size_t br = k<i2 ? k : i2;
      size_t mik = matpos2(i,k);
      size_t mik2 = matpos2(i,k2);

#if defined(FLOYDOPT)
      mik_index = m->m[mik];
      mik2_index = m->m[mik2];
      if(!(mik_index == 2 && mik2_index == 2)) {
#endif
	bound_set(ik,*getdbm(m,mik));
	bound_set(ik2,*getdbm(m,mik2));
	for (j=0;j<=br;j++) {
	  size_t kj = matpos(k,j);
	  size_t k2j = matpos(k2,j);
#if defined(FLOYDOPT)
	  mkj_index = m->m[kj];
	  mk2j_index = m->m[k2j];
	  if(!(mkj_index == 2 && mk2j_index == 2)) {
#endif
#if defined(FLOYDOPT)
	    myadd2(ij, ik, mkj_index);
#else
	    bound_add(ij,ik,*getdbm(m,kj));    /* ik+kj */
#endif
	    
	    setdbmbmin(m,matpos2(i,j), ij);
	    
#if defined(FLOYDOPT)
	    myadd2(ij,ik2,mk2j_index);
#else
	    bound_add(ij,ik2,*getdbm(m,k2j));  /* ik2+k2j */
#endif
	  
	    setdbmbmin(m,matpos2(i,j),ij);
#if defined(FLOYDOPT)
	  }
#endif
	}
	for (;j<=i2;j++) {
	  size_t j2k2 = matpos(j^1, k2);
	  size_t j2k = matpos(j^1,k);
#if defined(FLOYDOPT)
	  mkj_index = m->m[j2k2];
	  mk2j_index = m->m[j2k];
	  if(!(mkj_index == 2 && mk2j_index == 2)) {
#endif
	  
#if defined(FLOYDOPT)
	    myadd2(ij,ik, mkj_index);
#else
	    bound_add(ij,ik,*getdbm(m,j2k2)); /* ik+kj */
#endif
	    setdbmbmin(m,matpos2(i,j),ij);
	  
#if defined(FLOYDOPT)
	    myadd2(ij,ik2,mk2j_index);
#else
	    bound_add(ij,ik2,*getdbm(m,j2k)); /* ik2+k2j */
#endif
	    setdbmbmin(m,matpos2(i,j) ,ij);
#if defined(FLOYDOPT)
	  }
#endif
	}
#if defined(FLOYDOPT)
      }
#endif
    }
  }
  
  bound_clear(ik); bound_clear(ik2); bound_clear(ij);
  
  return hmat_s_step(m,dim);
}

/* ============================================================ */
/* Incremental Closure */
/* ============================================================ */

/* m must equal to a closed matrix, except for constraints involving
   variable v

   Quadratic time. Constant space.
*/

bool hmat_close_binary_incremental_equality(oct_internal_t* pr, dbm* m, size_t dim, size_t b, size_t bara, bound_t d, bound_t dprime) {
  if (incrclosure_seq(m, dim, b, bara, d)) {
    return true;
  } else {
    return incrclosure_seq(m,dim,b^1, bara^1, dprime);
  }
}


bool hmat_close_binary_incremental_inequality(oct_internal_t* pr, dbm* m, size_t dim, size_t b, size_t bara, bound_t d) {
  return incrclosure_seq(m, dim, b, bara, d);
}

bool hmat_close_incremental(dbm* m, size_t dim, size_t v)
{
  size_t i,j,k;
  bound_t c;
  bound_t ij,ik,ik2;

  bound_init(ik); bound_init(ik2); bound_init(ij);
  bound_init(c);

  /* incremental Floyd-Warshall : v in end-point position */
  for (k=0;k<2*dim;k++) {
    size_t kk = k^1;
    size_t ii = 2*v+1;
    size_t br  = k<ii ? k : ii;
    for (i=2*v;i<2*v+2;i++) {
      /* v in first end-point position */
      bound_set(ik,*getdbm(m,matpos2(i,k)));
      bound_set(ik2,*getdbm(m,matpos2(i,kk)));
      for (j=0;j<=br;j++) {
	bound_set(c, *getdbm(m, matpos2(i,j)));
	bound_add(ij,ik,*getdbm(m,matpos(k,j)));    /* ik+kj */
	bound_bmin(c,ij);
	bound_add(ij,ik2,*getdbm(m,matpos(kk,j)));  /* ik2+k2j */
	bound_bmin(c,ij);
	setdbmbmin(m,matpos2(i,j), c);
      }
      for (;j<=ii;j++) {
	bound_set(c, *getdbm(m, matpos2(i,j)));
	bound_add(ij,ik,*getdbm(m,matpos(j^1,kk))); /* ik+kj */
	bound_bmin(c,ij);
	bound_add(ij,ik2,*getdbm(m,matpos(j^1,k))); /* ik2+k2j */
	bound_bmin(c,ij);
	setdbmbmin(m,matpos2(i,j), c);
      }
      /* v in second end-point position */   
      bound_set(ik,*getdbm(m,matpos2(k,i)));
      bound_set(ik2,*getdbm(m,matpos2(kk,i)));
      for (j=i;j<k;j++) {
	bound_set(c, *getdbm(m, matpos2(i,j)));
	bound_add(ij,ik,*getdbm(m,matpos(kk,j^1))); /* ik+kj */
	bound_bmin(c,ij);
	bound_add(ij,ik2,*getdbm(m,matpos(k,j^1))); /* ik2+k2j */
	bound_bmin(c,ij);
	setdbmbmin(m,matpos2(i,j), c);
      }
      for (;j<2*dim;j++) {
	bound_set(c, *getdbm(m, matpos2(i,j)));
	bound_add(ij,ik,*getdbm(m,matpos(j,k)));    /* ik+kj */
	bound_bmin(c,ij);
	bound_add(ij,ik2,*getdbm(m,matpos(j,kk)));  /* ik2+k2j */
	bound_bmin(c,ij);
	setdbmbmin(m,matpos2(i,j), c);
      }
    }
  }
  
  /* incremental Floyd-Warshall : v in pivot position */
  for (k=2*v;k<2*v+2;k++) {
    size_t kk = k^1;
    for (i=0;i<2*dim;i++) {
      size_t ii = i|1;
      size_t br = k<ii ? k : ii;
      bound_set(ik,*getdbm(m,matpos2(i,k)));
      bound_set(ik2,*getdbm(m,matpos2(i,kk)));
      for (j=0;j<=br;j++) {
	bound_set(c, *getdbm(m, matpos2(i,j)));
	bound_add(ij,ik,*getdbm(m,matpos(k,j)));    /* ik+kj */
	bound_bmin(c,ij);
	bound_add(ij,ik2,*getdbm(m,matpos(kk,j)));  /* ik2+k2j */
	bound_bmin(c,ij);
	setdbmbmin(m,matpos2(i,j), c);
      }
      for (;j<=ii;j++) {
	bound_set(c, *getdbm(m, matpos2(i,j)));
	bound_add(ij,ik,*getdbm(m,matpos(j^1,kk))); /* ik+kj */
	bound_bmin(c,ij);
	bound_add(ij,ik2,*getdbm(m,matpos(j^1,k))); /* ik2+k2j */
	bound_bmin(c,ij);
	setdbmbmin(m,matpos2(i,j), c);
      }
    } 
  }
  
  bound_clear(ik); bound_clear(ik2); bound_clear(ij);
  bound_clear(c);

  return hmat_s_step(m,dim);
}



/* ============================================================ */
/* Sanity Check */
/* ============================================================ */

bool hmat_check_closed(dbm* m, size_t dim)
{
  bool closed = true;
  size_t i,j,k;
  bound_t w;

  bound_init(w);

  for (i=0;i<2*dim;i++)
    for (j=0;j<2*dim;j++)
      if (bound_cmp(*getdbm(m,matpos2(i,j)),*getdbm(m,matpos2(j^1,i^1)))>0) closed = false;
    
  for (i=0;i<2*dim;i++)
    for (j=0;j<2*dim;j++) {
      bound_add(w,*getdbm(m,matpos2(i,i^1)),*getdbm(m,matpos2(j^1,j)));
      bound_div_2(w,w);
      if (bound_cmp(*getdbm(m,matpos2(i,j)),w)>0) closed = false;
    }

  bound_clear(w);

  return closed;
}

