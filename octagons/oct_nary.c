/*
 * oct_nary.c
 *
 * N-ary octagon functions: meet, join, widening, narrowing & related.
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

/* ============================================================ */
/* Meet and Join */
/* ============================================================ */

oct_t* oct_meet(ap_manager_t* man, bool destructive, oct_t* a1, oct_t* a2)
{

  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_MEET,0);
  
  dbm* m;
  arg_assert(a1->dim==a2->dim && a1->intdim==a2->intdim,return NULL;);
  if ((!a1->closed && !a1->m) || (!a2->closed && !a2->m))
    /* one argument is empty */
    return oct_set_mat(pr,a1,NULL,NULL,destructive);
  else {
    dbm* m1 = a1->closed ? a1->closed : a1->m;
    dbm* m2 = a2->closed ? a2->closed : a2->m;

    size_t i;
    m = destructive ? m1 : hmat_alloc(pr,a1->dim);
    for (i=0;i<matsize(a1->dim);i++)
      setdbmmin(m,i,*getdbm(m1,i),*getdbm(m2,i));
    /* optimal, but not closed */
    return oct_set_mat(pr,a1,m,NULL,destructive);
  }
}

oct_t* oct_join(ap_manager_t* man, bool destructive, oct_t* a1, oct_t* a2)
{
  
 oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_JOIN,0);
 arg_assert(a1->dim==a2->dim && a1->intdim==a2->intdim,return NULL;);
 if (pr->funopt->algorithm>=0) {
   oct_cache_closure(pr,a1);
   oct_cache_closure(pr,a2);
 }
 if (!a1->closed && !a1->m) {
   if (!a2->closed && !a2->m)
     /* both empty */
     return oct_set_mat(pr,a1,NULL,NULL,destructive);
   else
     /* a1 empty, a2 not empty */
     return oct_set_mat(pr,a1,hmat_copy(pr,a2->m,a2->dim),
			hmat_copy(pr,a2->closed,a2->dim),destructive);
 }
 else if (!a2->closed && !a2->m)
   /* a1 not empty, a2 empty */
   return oct_set_mat(pr,a1,a1->m,a1->closed,destructive);
 else {
   /* not empty */
   dbm* m1 = a1->closed ? a1->closed : a1->m;
   dbm* m2 = a2->closed ? a2->closed : a2->m;
   dbm* m = destructive ? m1 : hmat_alloc(pr,a1->dim);
   size_t i;
   man->result.flag_exact = false;
   for (i=0;i<matsize(a1->dim);i++) {
     
#if defined(FLOYDOPT) || defined(JOINOPT) 
     mysetdbmmax(m,i,m1,m2);
#else  
     setdbmmax(m,i,*getdbm(m1,i),*getdbm(m2,i)); 
#endif  
   }
   if (a1->closed && a2->closed) {
     /* result is closed and optimal on Q */
     if (num_incomplete || a1->intdim) flag_incomplete;
     return oct_set_mat(pr,a1,NULL,m,destructive);
   }
   else {
     /* not optimal, not closed */
     flag_algo;
     return oct_set_mat(pr,a1,m,NULL,destructive); 
   }
 }
}

oct_t* oct_meet_array(ap_manager_t* man, oct_t** tab, size_t size)
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_MEET_ARRAY,0);
  oct_t* r;
  size_t i,k;
  arg_assert(size>0,return NULL;);
  r = oct_alloc_internal(pr,tab[0]->dim,tab[0]->intdim);
  /* check whether there is an empty element */
  for (k=0;k<size;k++)
    if (!tab[k]->m && !tab[k]->closed) return r;
  /* all elements are non-empty */
  r->m = hmat_copy(pr,tab[0]->closed ? tab[0]->closed : tab[0]->m,r->dim);
  for (k=1;k<size;k++) {
    dbm* x = tab[k]->closed ? tab[k]->closed : tab[k]->m;
    arg_assert(tab[k]->dim==r->dim && tab[k]->intdim==r->intdim,
	       oct_free_internal(pr,r);return NULL;);
    for (i=0;i<matsize(r->dim);i++)
      setdbmbmin(r->m,i,*getdbm(x,i));
  }
  return r;
}

oct_t* oct_join_array(ap_manager_t* man, oct_t** tab, size_t size)
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_JOIN_ARRAY,0);
  int algo = pr->funopt->algorithm;
  bool closed = true;
  oct_t* r;
  dbm* m = NULL;
  size_t i,k;
  arg_assert(size>0,return NULL;);
  r = oct_alloc_internal(pr,tab[0]->dim,tab[0]->intdim);
  for (k=0;k<size;k++) {
    arg_assert(tab[k]->dim==r->dim && tab[k]->intdim==r->intdim,
	       oct_free_internal(pr,r);return NULL;);
    if (algo>=0) oct_cache_closure(pr,tab[k]);
    /* skip definitely empty */
    if (!tab[k]->m && !tab[k]->closed) continue;
    if (!m)
      /* first non-empty */
      m = hmat_copy(pr,tab[k]->closed ? tab[k]->closed : tab[k]->m,r->dim);
    else {
      /* not first non-empty */
      dbm* x = tab[k]->closed ? tab[k]->closed : tab[k]->m;
      for (i=0;i<matsize(r->dim);i++)
	setdbmbmax(m,i,*getdbm(x,i));
    }
    if (!tab[k]->closed) closed = false;
  }

  if (!m) {
    /* empty result */
  }
  else if (closed) { 
    /* closed, optimal result, in Q */
    man->result.flag_exact = false;
    r->closed = m; 
    if (num_incomplete || r->intdim) flag_incomplete;
  }
  else {
    /* non closed, non optimal result */
    r->m = m;
    flag_algo; 
  }
  return r;
}



/* ============================================================ */
/* Widening, Narrowing */
/* ============================================================ */

oct_t* oct_widening(ap_manager_t* man, oct_t* a1, oct_t* a2)
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_WIDENING,0);
  int algo = pr->funopt->algorithm;
  oct_t* r;
  arg_assert(a1->dim==a2->dim && a1->intdim==a2->intdim,return NULL;);
  if (algo>=0) oct_cache_closure(pr,a2);
  if (!a1->closed && !a1->m)
    /* a1 definitively closed */
    r = oct_copy_internal(pr,a2);
  else if (!a2->closed && !a2->m)
   /* a2 definitively closed */
    r = oct_copy_internal(pr,a1);
  else {
    /* work on the origial left matrix, not the closed cache! */
    dbm* m1 = a1->m ? a1->m : a1->closed;
    dbm* m2 = a2->closed ? a2->closed : a2->m;
    size_t i;
    r = oct_alloc_internal(pr,a1->dim,a1->intdim);
    r->m = hmat_alloc(pr,r->dim);
    if (algo==oct_pre_widening || algo==-oct_pre_widening) {
      /* degenerate hull: NOT A PROPER WIDENING, use with care */
      for (i=0;i<matsize(r->dim);i++)
#if defined(FLOYDOPT) || defined(JOINOPT)
	mysetdbmmax(r->m,i,m1,m2);
#else
	setdbmmax(r->m,i,*getdbm(m1,i),*getdbm(m2,i));
#endif
    }
    else {
      /* standard widening */
      for (i=0;i<matsize(r->dim);i++)
	if (bound_cmp(*getdbm(m1,i),*getdbm(m2,i))>=0)
	  setdbm(r->m,i,*getdbm(m1,i));
	  /* bound_set(*getdbm(r->m,i),*getdbm(m1,i)); */
	else setdbminfty(r->m,i);
    }
  }
  return r;
}

oct_t* oct_widening_thresholds(ap_manager_t* man,
			       oct_t* a1, oct_t* a2,
			       ap_scalar_t** array,
			       size_t nb)
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_WIDENING,nb+1);
  int algo = pr->funopt->algorithm;
  oct_t* r;
  arg_assert(a1->dim==a2->dim && a1->intdim==a2->intdim,return NULL;);
  if (algo>=0) oct_cache_closure(pr,a2);
  if (!a1->closed && !a1->m)
    /* a1 definitively closed */
    r = oct_copy_internal(pr,a2);
  else if (!a2->closed && !a2->m)
   /* a2 definitively closed */
    r = oct_copy_internal(pr,a1);
  else {
    /* work on the origial left matrix, not the closed cache! */
    dbm* m1 = a1->m ? a1->m : a1->closed;
    dbm* m2 = a2->closed ? a2->closed : a2->m;
    size_t i;
    r = oct_alloc_internal(pr,a1->dim,a1->intdim);
    r->m = hmat_alloc(pr,r->dim);
    /* convert array to bounds */
    for (i=0;i<nb;i++)
      bound_of_scalar(pr,pr->tmp[i],array[i],false,false);
    bound_set_infty(pr->tmp[nb],1);
    /* point-wise loop */
    for (i=0;i<matsize(r->dim);i++) 
      if (bound_cmp(*getdbm(m1,i),*getdbm(m2,i))>=0) {
	setdbm(r->m,i,*getdbm(m1,i));
      }
      else {
#if 0
	/* dichotomy on array */
	size_t low=0, hi=nb;
	while (low<hi) {
	  size_t med = (low+hi)/2;
	  if (bound_cmp(pr->tmp[med],m2[i])<0) low=med+1;
	  else hi=med;
	}
	setdbm(r->m, i, pr->tmp[low]);
#else
	size_t j;
	for (j=0;j<nb;j++)
	  if (bound_cmp(*getdbm(m2,i),pr->tmp[j])<=0) break;
	setdbm(r->m, i, pr->tmp[j]);
#endif
      }
    /* warn user for conv errors in thresolds */
    if (pr->conv) flag_conv;
  }
  return r;
}

oct_t* oct_narrowing(ap_manager_t* man, oct_t* a1, oct_t* a2)
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_WIDENING,0);
  oct_t* r;
  arg_assert(a1->dim==a2->dim && a1->intdim==a2->intdim,return NULL;);
  if (pr->funopt->algorithm>=0) {
    oct_cache_closure(pr,a1);
    oct_cache_closure(pr,a2);
  }
  r = oct_alloc_internal(pr,a1->dim,a1->intdim);
  if ((!a1->closed && !a1->m) || (!a2->closed && !a2->m)) {
    /* a1 or a2 definitively closed */
  }
  else {
    dbm* m1 = a1->closed ? a1->closed : a1->m;
    dbm* m2 = a2->closed ? a2->closed : a2->m;
    size_t i;
    r->m = hmat_alloc(pr,r->dim);
    for (i=0;i<matsize(r->dim);i++)
      //bound_set(*getdbm(r->m,i), bound_infty(*getdbm(m1,i)) ? *getdbm(m2,i) : *getdbm(m1,i));
      setdbm(r->m, i, bound_infty(*getdbm(m1,i)) ? *getdbm(m2,i) : *getdbm(m1,i));
  }
  return r;
}

ap_abstract0_t* ap_abstract0_oct_narrowing( ap_manager_t* man,
					    ap_abstract0_t* a1,
					    ap_abstract0_t* a2 )
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_WIDENING,0);
  oct_t* a = (oct_t*) (a1->value);
  arg_assert(man->library==a1->man->library &&
	     man->library==a2->man->library,
	     return abstract0_of_oct(man,oct_alloc_top(pr,a->dim,a->intdim)););
  return abstract0_of_oct(man,oct_narrowing
			  (man,a1->value,a2->value));
}

ap_abstract0_t* 
ap_abstract0_oct_widening_thresholds(ap_manager_t* man,
				     ap_abstract0_t* a1, 
				     ap_abstract0_t* a2,
				     ap_scalar_t** array,
				     size_t nb)
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_WIDENING,0);
  oct_t* a = (oct_t*) (a1->value);
  arg_assert(man->library==a1->man->library &&
	     man->library==a2->man->library,
	     return abstract0_of_oct(man,oct_alloc_top(pr,a->dim,a->intdim)););
  return 
    abstract0_of_oct(man,oct_widening_thresholds
		     (man,a1->value,a2->value,array,nb));
}


/* ============================================================ */
/* Perturbation */
/* ============================================================ */

oct_t* oct_add_epsilon(ap_manager_t* man, oct_t* a, ap_scalar_t* epsilon)
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_WIDENING,2);
  oct_t* r = oct_alloc_internal(pr,a->dim,a->intdim);
  dbm* m;
  m = a->m ? a->m : a->closed;
  if (m) {
    size_t i;
    /* compute max of finite bounds */
    bound_set_int(pr->tmp[0],0);
    for (i=0;i<matsize(a->dim);i++) {
      if (bound_infty(*getdbm(m,i))) continue;
      if (bound_sgn(*getdbm(m,i))>=0) 
	bound_max(pr->tmp[0],pr->tmp[0],*getdbm(m,i));
      else {
	bound_neg(pr->tmp[1],*getdbm(m,i));
	bound_max(pr->tmp[0],pr->tmp[0],pr->tmp[1]);
      }
    }
    /* multiply by epsilon */
    bound_of_scalar(pr,pr->tmp[1],epsilon,false,false);
    bound_mul(pr->tmp[0],pr->tmp[0],pr->tmp[1]);
    /* enlarge bounds */
    r->m = hmat_alloc(pr,r->dim);
    for (i=0;i<matsize(r->dim);i++)
      setdbmbadd(r->m, i, pr->tmp[0]);
      /* bound_add(*getdbm(r->m,i),*getdbm(m,i),pr->tmp[0]); */
  }
  return r;
}

ap_abstract0_t* 
ap_abstract0_oct_add_epsilon(ap_manager_t* man, 
			     ap_abstract0_t* a1, 
			     ap_scalar_t* epsilon)
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_WIDENING,0);
  oct_t* a = (oct_t*) (a1->value);
  arg_assert(man->library==a1->man->library,
	     return abstract0_of_oct(man,oct_alloc_top(pr,a->dim,a->intdim)););
  return abstract0_of_oct(man,oct_add_epsilon(man,a,epsilon));
}


oct_t* oct_add_epsilon_bin(ap_manager_t* man, oct_t* a1, oct_t* a2, 
			   ap_scalar_t* epsilon)
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_WIDENING,2);
  oct_t* r;
  arg_assert(a1->dim==a2->dim && a1->intdim==a2->intdim,return NULL;);
  if (!a1->closed && !a1->m)
    /* a1 definitely empty */
    r = oct_copy_internal(pr,a2);
  else if (!a2->closed && !a2->m)
    /* a2 definitely empty */
    r = oct_copy_internal(pr,a1);
  else {
    dbm* m1 = a1->m ? a1->m : a1->closed;
    dbm* m2 = a2->m ? a2->m : a2->closed;
    size_t i;
    r = oct_alloc_internal(pr,a1->dim,a1->intdim);
    r->m = hmat_alloc(pr,r->dim);
    /* get max abs of non +oo coefs in m2, times epsilon */
    bound_set_int(pr->tmp[0],0);
    for (i=0;i<matsize(a1->dim);i++) {
      if (bound_infty(*getdbm(m2,i))) continue;
      if (bound_sgn(*getdbm(m2,i))>=0) 
	bound_max(pr->tmp[0],pr->tmp[0],*getdbm(m2,i));
      else {
	bound_neg(pr->tmp[1],*getdbm(m2,i));
	bound_max(pr->tmp[0],pr->tmp[0],pr->tmp[1]);
      }
    }
    /* multiply by epsilon */
    bound_of_scalar(pr,pr->tmp[1],epsilon,false,false);
    bound_mul(pr->tmp[0],pr->tmp[0],pr->tmp[1]);
    /* enlarge unstable coefficients in a1 */
    for (i=0;i<matsize(a1->dim);i++)
      if (bound_cmp(*getdbm(m1,i),*getdbm(m2,i))<0)
	setdbmadd(r->m,i,*getdbm(m2,i),pr->tmp[0]);
	/* bound_add(*getdbm(r->m,i),*getdbm(m2,i),pr->tmp[0]); */
      else
	setdbm(r->m,i,*getdbm(m1,i));
	/* bound_set(*getdbm(r->m,i),*getdbm(m1,i)); */
  }
  return r;
}

ap_abstract0_t* 
ap_abstract0_oct_add_epsilon_bin(ap_manager_t* man, 
				 ap_abstract0_t* a1, 
				 ap_abstract0_t* a2, 
				 ap_scalar_t* epsilon)
{
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_WIDENING,0);
  oct_t* a = (oct_t*) (a1->value);
  arg_assert(man->library==a1->man->library &&
	     man->library==a2->man->library,
	     return abstract0_of_oct(man,oct_alloc_top(pr,a->dim,a->intdim)););
  return abstract0_of_oct(man,oct_add_epsilon_bin(man,a1->value,a2->value,epsilon));
}

