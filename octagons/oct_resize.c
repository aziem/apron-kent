/*
 * oct_resize.c
 *
 * Projection, changes of dimension, variable permutation.
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
#include "logging.h"


/* ============================================================ */
/* Projections */
/* ============================================================ */

oct_t* oct_forget_array(ap_manager_t* man,
			bool destructive, oct_t* a,
			ap_dim_t* tdim, size_t size,
			bool project)
{
#if defined(OCTINCRDEBUG)
  startfuncdebug(__func__);
#endif

  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_FORGET_ARRAY,0);
  if (pr->funopt->algorithm>=0) oct_cache_closure(pr,a);
  if (!a->closed && !a->m)
    /* definitively empty */
    return oct_set_mat(pr,a,NULL,NULL,destructive);
  else {
    dbm* m = a->closed ? a->closed : a->m;
    size_t i,k;
    if (!destructive) m = hmat_copy(pr,m,a->dim);
    for (i=0;i<size;i++) {
      ap_dim_t d2 = 2*tdim[i];
      arg_assert(tdim[i]<a->dim,return NULL;);
      /* binary constraints on tdim[i] */
      for (k=0;k<d2;k++) {
	/* bound_set_infty(*getdbm(m,matpos(d2,k)),1); */
	/* bound_set_infty(*getdbm(m,matpos(d2+1,k)),1); */
	setdbminfty(m,matpos(d2,k));
	setdbminfty(m,matpos(d2+1,k));
      }
      for (k=d2+2;k<2*a->dim;k++) {
	/* bound_set_infty(*getdbm(m,matpos(k,d2)),1); */
	/* bound_set_infty(*getdbm(m,matpos(k,d2+1)),1); */
	setdbminfty(m,matpos(k,d2));
	setdbminfty(m,matpos(k,d2+1));
      }
      /* unary constraints on tdim[i] */
      if (project) {
	/* bound_set_int(*getdbm(m,matpos(d2,d2+1)),0); */
	/* bound_set_int(*getdbm(m,matpos(d2+1,d2)),0); */
	setdbmzero(m,matpos(d2,d2+1));
	setdbmzero(m,matpos(d2+1,d2));
      }
      else {
	setdbminfty(m,matpos(d2,d2+1));
	setdbminfty(m,matpos(d2+1,d2));
      }
    }
    if (a->closed) {
      /* result is exact on Q, and closed if forget, not project */
      if (num_incomplete || a->intdim) flag_incomplete;
      if (project) return oct_set_mat(pr,a,m,NULL,destructive);
      else return oct_set_mat(pr,a,NULL,m,destructive);
    }
    else {
      /* not exact, not closed */
      flag_algo;
      return oct_set_mat(pr,a,m,NULL,destructive);
    }
  }
}


/* ============================================================ */
/* Change and permutation of dimensions */
/* ============================================================ */

/* internal helper function */
// TODO CHANGE THIS
void hmat_addrem_dimensions_boundarray(dbm* dst, bound_t* src,
			    ap_dim_t* pos, size_t nb_pos,
			    size_t mult, size_t dim, bool add)
{
#if defined(OCTINCRDEBUG)
  startfuncdebug(__func__);
#endif
  size_t i,j,new_j,org_j;
  new_j = org_j = pos[0]*2;
  //bound_set_array(dst,src,matsize(pos[0]));
  dbm_bound_set_array2(dst,src,matsize(pos[0]));
  
  for (j=0;j<nb_pos;j++) {
    /* skip lines */
    if (add) new_j += 2*mult; else org_j += 2*mult;
    
    /* copy lines */
    {
      bound_t* org_c = src+matsize(org_j/2);
      bound_t* new_c = getdbm(dst,matsize(new_j/2));
      size_t last_org_j = ((j<nb_pos-1) ? pos[j+1] : dim)*2;
      for (;org_j<last_org_j;org_j++,new_j++) {
	size_t size_org_line = org_j+2-(org_j&1);
	size_t size_new_line = new_j+2-(new_j&1);
	size_t org_i = 0;
	size_t new_i = 0;
	for (i=0;i<nb_pos;i++) {
	  /* copy elems */
	  size_t last_org_i = pos[i]*2;
	  if (last_org_i>=size_org_line) break; /* partial block */
	  bound_set_array(new_c+new_i,org_c+org_i,last_org_i-org_i);
	  new_i += last_org_i-org_i;
	  org_i = last_org_i;
	  
	  /* skip elems */
	  if (add) new_i += 2*mult; else org_i += 2*mult;
	}
	
	/* copy remaining elems */
	bound_set_array(new_c+new_i,org_c+org_i,size_org_line-org_i);
	
	/* next line */
	org_c += size_org_line;
	new_c += size_new_line;
      }
    }
  }

#if defined(OCTINCRDEBUG)
  endfuncdebug(__func__);
#endif
}

/* void hmat_addrem_dimensions(dbm* dst, dbm* src, */
/* 			    ap_dim_t* pos, size_t nb_pos, */
/* 			    size_t mult, size_t dim, bool add) */
/* { */
/*   printf("HERE I AM\n"); */
/*   size_t i,j,new_j,org_j; */
/*   new_j = org_j = pos[0]*2; */
/*   //bound_set_array(dst,src,matsize(pos[0])); */
/*   dbm_set_array(dst,src,matsize(pos[0])); */
  
/*   for (j=0;j<nb_pos;j++) { */
/*     /\* skip lines *\/ */
/*     if (add) new_j += 2*mult; else org_j += 2*mult; */
    
/*     /\* copy lines *\/ */
/*     { */
/*       bound_t* org_c = getdbm(src, matsize(org_j/2)); */
/*       bound_t* new_c = getdbm(dst, matsize(new_j/2)); */
/*       size_t last_org_j = ((j<nb_pos-1) ? pos[j+1] : dim)*2; */
/*       for (;org_j<last_org_j;org_j++,new_j++) { */
/* 	size_t size_org_line = org_j+2-(org_j&1); */
/* 	size_t size_new_line = new_j+2-(new_j&1); */
/* 	size_t org_i = 0; */
/* 	size_t new_i = 0; */
/* 	for (i=0;i<nb_pos;i++) { */
/* 	  /\* copy elems *\/ */
/* 	  size_t last_org_i = pos[i]*2; */
/* 	  if (last_org_i>=size_org_line) break; /\* partial block *\/ */
/* 	  bound_set_array(new_c+new_i,org_c+org_i,last_org_i-org_i); */
/* 	  new_i += last_org_i-org_i; */
/* 	  org_i = last_org_i; */
	  
/* 	  /\* skip elems *\/ */
/* 	  if (add) new_i += 2*mult; else org_i += 2*mult; */
/* 	} */
	
/* 	/\* copy remaining elems *\/ */
/* 	bound_set_array(new_c+new_i,org_c+org_i,size_org_line-org_i); */
	
/* 	/\* next line *\/ */
/* 	org_c += size_org_line; */
/* 	new_c += size_new_line; */
/*       } */
/*     } */
/*   } */
/* } */

void hmat_addrem_dimensions(dbm* dst, dbm* src, 
			    ap_dim_t* pos, size_t nb_pos,
			    size_t mult, size_t dim, bool add)
{
#if defined(OCTINCRDEBUG)
  startfuncdebug(__func__);
#endif

  size_t i,j,new_j,org_j;
  new_j = org_j = pos[0]*2;
  //bound_set_array(dst,src,matsize(pos[0]));
  dbm_set_array(dst,src,matsize(pos[0]));
  
  for (j=0;j<nb_pos;j++) {
    /* skip lines */
    if (add) new_j += 2*mult; else org_j += 2*mult;
    
    /* copy lines */
    {
      //bound_t* org_c = getdbm(src, matsize(org_j/2));
      //bound_t* new_c = getdbm(dst, matsize(new_j/2));
      size_t org_c = matsize(org_j/2);
      size_t new_c = matsize(new_j/2);

      size_t last_org_j = ((j<nb_pos-1) ? pos[j+1] : dim)*2;
      for (;org_j<last_org_j;org_j++,new_j++) {
	size_t size_org_line = org_j+2-(org_j&1);
	size_t size_new_line = new_j+2-(new_j&1);
	size_t org_i = 0;
	size_t new_i = 0;
	for (i=0;i<nb_pos;i++) {
	  /* copy elems */
	  size_t last_org_i = pos[i]*2;
	  if (last_org_i>=size_org_line) break; /* partial block */
	  //bound_set_array(new_c+new_i,org_c+org_i,last_org_i-org_i);
	  dbm_set_array_from_point(dst, src, new_c+new_i, org_c+org_i, last_org_i-org_i);
	  new_i += last_org_i-org_i;
	  org_i = last_org_i;
	  
	  /* skip elems */
	  if (add) new_i += 2*mult; else org_i += 2*mult;
	}
	
	/* copy remaining elems */
	//bound_set_array(new_c+new_i,org_c+org_i,size_org_line-org_i);
	dbm_set_array_from_point(dst, src, new_c+new_i, org_c+org_i, size_org_line-org_i);
	
	/* next line */
	org_c += size_org_line;
	new_c += size_new_line;
      }
    }
  }
  
#if defined(OCTINCRDEBUG)
  endfuncdebug(__func__);
#endif
}




oct_t* oct_add_dimensions(ap_manager_t* man,
			  bool destructive, oct_t* a,
			  ap_dimchange_t* dimchange,
			  bool project)
{
#if defined(OCTINCRDEBUG)
  startfuncdebug(__func__);
#endif
 
  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_ADD_DIMENSIONS,0);
  dbm* m = a->closed ? a->closed : a->m;
  dbm* mm;
  size_t i, nb = dimchange->intdim+dimchange->realdim;
  oct_t* r;
  if (!m) mm = NULL;
  else {
    /* check */
    for (i=0;i<nb;i++) {
      arg_assert(dimchange->dim[i]<=a->dim,return NULL;);
      arg_assert(!i || dimchange->dim[i-1]<=dimchange->dim[i],return NULL;);
    }
    
    /* insert variables */
    mm = hmat_alloc_top(pr,a->dim+nb);
    hmat_addrem_dimensions(mm,m,dimchange->dim,
			   nb,1,a->dim,true);

    /* set new variables to 0, if necessary */
    if (project) {
      for (i=0;i<nb;i++) {
	size_t v = 2*(i+dimchange->dim[i]);
	/* bound_set_int(*getdbm(mm,matpos(v+1,v)),0); */
	/* bound_set_int(*getdbm(mm,matpos(v,v+1)),0); */
	setdbmzero(mm,matpos(v+1,v));
	setdbmzero(mm,matpos(v,v+1));
      }
    }
  }
  /* always exact, respect closure if embedding, not projecting */
  if (a->closed && !project) r = oct_set_mat(pr,a,NULL,mm,destructive);
  else r = oct_set_mat(pr,a,mm,NULL,destructive);
  r->dim += nb;
  r->intdim += dimchange->intdim;
#if defined(OCTINCRDEBUG)
  endfuncdebug(__func__);
#endif
  return r;
}

oct_t* oct_remove_dimensions(ap_manager_t* man,
			     bool destructive, oct_t* a,
			     ap_dimchange_t* dimchange)
{
#if defined(OCTINCRDEBUG)
  startfuncdebug(__func__);
#endif

  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_REMOVE_DIMENSIONS,0);
  dbm *m, *mm;
  size_t i, nb = dimchange->intdim+dimchange->realdim;
  oct_t* r;
  if (pr->funopt->algorithm>=0) oct_cache_closure(pr,a);
  m = a->closed ? a->closed : a->m;
  if (!m) mm = NULL;
  else {
    /* check */
    for (i=0;i<nb;i++) {
      arg_assert(dimchange->dim[i]<a->dim,return NULL;);
      arg_assert(!i || dimchange->dim[i-1]<dimchange->dim[i],return NULL;);
    }

    /* remove variables */
    mm = hmat_alloc(pr,a->dim-nb);
    hmat_addrem_dimensions(mm,m,dimchange->dim,
			   nb,1,a->dim,false);
  }

  if (a->closed) {
    /* result is exact on Q, and closed */
    if (num_incomplete || a->intdim) flag_incomplete;
    r = oct_set_mat(pr,a,NULL,mm,destructive);
  }
  else {
    /* not exact, not closed */
    flag_algo;
    r = oct_set_mat(pr,a,mm,NULL,destructive);
  }
  r->dim -= nb;
  r->intdim -= dimchange->intdim;
#if defined(OCTINCRDEBUG)
  endfuncdebug(__func__);
#endif
  return r;
}

/* internal helper function: permute & change dimension */
void hmat_permute(dbm* dst, dbm* src,
		  size_t dst_dim, size_t src_dim,
		  ap_dim_t* permutation)
{
#if defined(OCTINCRDEBUG)
  startfuncdebug(__func__);
#endif

  size_t i,j;
  size_t index;
  index = 0;
  for (i=0;i<src_dim;i++) {
    size_t new_ii = 2*permutation[i];
    /* if (new_ii >= 2*dst_dim)  { src+=4*(i+1); continue; } */
    if (new_ii >= 2*dst_dim)  { index+=4*(i+1); continue; }
    /* for (j=0;j<=i;j++, src+=2) { */
    for (j=0;j<=i;j++, index+=2) {
      size_t new_jj = 2*permutation[j];
      if (new_jj >= 2*dst_dim) continue;
      setdbm(dst, matpos2(new_ii, new_jj), *getdbm(src, index+0));
      setdbm(dst,matpos2(new_ii  ,new_jj+1),*getdbm(src,index+1));
      setdbm(dst,matpos2(new_ii+1,new_jj),*getdbm(src,index+2*(i+1)));
      setdbm(dst,matpos2(new_ii+1,new_jj+1),*getdbm(src,index+2*(i+1)+1));
    }
    /* src+=2*(i+1); */
    index+=2*(i+1);
  }
#if defined(OCTINCRDEBUG)
  endfuncdebug(__func__);
#endif
}

oct_t* oct_permute_dimensions(ap_manager_t* man,
			      bool destructive, oct_t* a,
			      ap_dimperm_t* permutation)
{
#if defined(OCTINCRDEBUG)
  startfuncdebug(__func__);
#endif

  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_ADD_DIMENSIONS,0);
  dbm* m = a->closed ? a->closed : a->m;
  dbm* mm;
  arg_assert(permutation->size==a->dim,return NULL;);
  if (!m) mm = NULL;
  else {
    /* check (only bounds, not injectivity) */
    size_t i,j;
    for (i=0;i<a->dim;i++)
      arg_assert(permutation->dim[i]<a->dim,return NULL;);
    
    /* permuted copy */
    mm = hmat_alloc(pr,a->dim);
    hmat_permute(mm,m,a->dim,a->dim,permutation->dim);
  }
  /* always exact, respects closure */
  if (a->closed) return oct_set_mat(pr,a,NULL,mm,destructive);
  else return oct_set_mat(pr,a,mm,NULL,destructive);
}


/* ============================================================ */
/* Expansion and folding of dimensions */
/* ============================================================ */

oct_t* oct_expand(ap_manager_t* man,
		  bool destructive, oct_t* a,
		  ap_dim_t dim,
		  size_t n)
{
#if defined(OCTINCRDEBUG)
  startfuncdebug(__func__);
#endif


  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_EXPAND,0);
  dbm* m = a->closed ? a->closed : a->m;
  size_t i, j;
  ap_dim_t pos = (dim < a->intdim) ? a->intdim : a->dim;
  dbm* mm;
  oct_t* r;
  arg_assert(dim<a->dim,return NULL;);
  if (!m) mm = NULL;
  else {
    /* insert n variables at pos */
    mm = hmat_alloc_top(pr,a->dim+n);
    hmat_addrem_dimensions(mm,m,&pos,1,n,a->dim,true);

    for (i=0;i<n;i++) {

      /* copy binary constraints */

      for (j=0;j<2*dim;j++) {
	/* bound_set(*getdbm(mm,matpos2(2*(pos+i)  ,j)),*getdbm(mm,matpos(2*dim  ,j))); */
	/* bound_set(*getdbm(mm,matpos2(2*(pos+i)+1,j)),*getdbm(mm,matpos(2*dim+1,j))); */
	setdbm(mm,matpos2(2*(pos+i) ,j),*getdbm(mm,matpos(2*dim  ,j)));
	setdbm(mm,matpos2(2*(pos+i)+1,j),*getdbm(mm,matpos(2*dim+1,j)));
      }
      for (j=2*dim+2;j<2*(a->dim+n);j++) {
	/* bound_set(*getdbm(mm,matpos2(2*(pos+i)  ,j)),*getdbm(mm,matpos(j^1,2*dim+1))); */
	/* bound_set(*getdbm(mm,matpos2(2*(pos+i)+1,j)),*getdbm(mm,matpos(j^1,2*dim))); */
	setdbm(mm,matpos2(2*(pos+i)  ,j),*getdbm(mm,matpos(j^1,2*dim+1)));
	setdbm(mm,matpos2(2*(pos+i)+1,j),*getdbm(mm,matpos(j^1,2*dim)));
      }

      /* copy unary constraints */
      /* bound_set(*getdbm(mm,matpos2(2*(pos+i),2*(pos+i)+1)),*getdbm(mm,matpos2(2*dim,2*dim+1))); */
      /* bound_set(*getdbm(mm,matpos2(2*(pos+i)+1,2*(pos+i))),*getdbm(mm,matpos2(2*dim+1,2*dim))); */
      setdbm(mm,matpos2(2*(pos+i),2*(pos+i)+1),*getdbm(mm,matpos2(2*dim,2*dim+1)));
      setdbm(mm,matpos2(2*(pos+i)+1,2*(pos+i)),*getdbm(mm,matpos2(2*dim+1,2*dim)));
    }
  }
  
  /*  exact, generally not closed */
  r = oct_set_mat(pr,a,mm,NULL,destructive);
  r->dim += n;
  if (dim<a->intdim) r->intdim += n;
#if defined(OCTINCRDEBUG)
  endfuncdebug(__func__);
#endif
  return r;
}

oct_t* oct_fold(ap_manager_t* man,
		bool destructive, oct_t* a,
		ap_dim_t* tdim,
		size_t size)
{
#if defined(OCTINCRDEBUG)
  startfuncdebug(__func__);
#endif

  oct_internal_t* pr = oct_init_from_manager(man,AP_FUNID_FOLD,matsize(a->dim));
  dbm* m;
  dbm* mm;
  oct_t* r;
  if (pr->funopt->algorithm>=0) oct_cache_closure(pr,a);
  m = a->closed ? a->closed : a->m;
  if (!m) mm = NULL;
  else {
    /* check, assuming tdim[0..(size-1)] is strictly increasing */
    size_t i,j;
    arg_assert(size>0,return NULL;);
    for (i=1;i<size;i++) {
      arg_assert(tdim[i-1]<tdim[i],return NULL;);
    }
    arg_assert(tdim[size-1]<a->dim,return NULL;);
    
    dbm_bound_set_array(pr->tmp,m,matsize(a->dim));

    /* merge binary constraints */
    for (j=0;j<2*tdim[0];j++) {
      bound_t* mm1 = pr->tmp+matpos2(tdim[0]*2  ,j);
      bound_t* mm2 = pr->tmp+matpos2(tdim[0]*2+1,j);
      for (i=1;i<size;i++) {
	bound_max(*mm1,*mm1,*getdbm(m,matpos2(tdim[i]*2  ,j)));
	bound_max(*mm2,*mm2,*getdbm(m,matpos2(tdim[i]*2+1,j)));
      }
    }
    for (j=2*(tdim[0]+1);j<2*a->dim;j++) {
      bound_t* mm1 = pr->tmp+matpos2(tdim[0]*2  ,j);
      bound_t* mm2 = pr->tmp+matpos2(tdim[0]*2+1,j);
      for (i=1;i<size;i++) {
	bound_max(*mm1,*mm1,*getdbm(m,matpos2(tdim[i]*2  ,j)));
	bound_max(*mm2,*mm2,*getdbm(m,matpos2(tdim[i]*2+1,j)));
      }
    }

    /* merge unary constraints */
    {
      bound_t* mm1 = pr->tmp+matpos2(tdim[0]*2  ,tdim[0]*2+1);
      bound_t* mm2 = pr->tmp+matpos2(tdim[0]*2+1,tdim[0]*2  );
      for (i=1;i<size;i++) {
	bound_max(*mm1,*mm1,*getdbm(m,matpos2(tdim[i]*2,tdim[i]*2+1)));
	bound_max(*mm2,*mm2,*getdbm(m,matpos2(tdim[i]*2+1,tdim[i]*2)));
      }
    }

    /* destroy all dimensions in tdim except the first one */
    mm = hmat_alloc_top(pr,a->dim-size+1);
    hmat_addrem_dimensions_boundarray(mm,pr->tmp,tdim+1,size-1,1,a->dim,false);

    /* reset diagonal elements */
    /* bound_set_int(*getdbm(mm,matpos(tdim[0]*2  ,tdim[0]*2  )),0); */
    /* bound_set_int(*getdbm(mm,matpos(tdim[0]*2+1,tdim[0]*2+1)),0); */
    setdbmzero(mm,matpos(tdim[0]*2  ,tdim[0]*2  ));
    setdbmzero(mm,matpos(tdim[0]*2+1,tdim[0]*2+1));

    man->result.flag_exact = false;
  }

  if (a->closed) {
    /* result is optimal on Q, not closed */
    if (num_incomplete || a->intdim) flag_incomplete;
    r = oct_set_mat(pr,a,mm,NULL,destructive);
  }
  else {
    /* not exact, not closed */
    flag_algo;
    r = oct_set_mat(pr,a,mm,NULL,destructive);
  }
  r->dim -= size-1;
  if (tdim[0]<r->intdim) r->intdim -= size-1;
#if defined(OCTINCRDEBUG)
  endfuncdebug(__func__);
#endif
  return r;
}
