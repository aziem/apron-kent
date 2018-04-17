#include "oct.h"
#include "oct_internal.h"


bound_t temp5; 
bound_t temp3;
bound_t temp4;
bound_t temp6;
bound_t mibari; 


int single_seq_helper(dbm* m, dbm* old, size_t dim, size_t start, size_t end, size_t a, size_t b, bound_t d, bound_t temp1, bound_t temp2) {
  if(!istempallocd) {
    bound_init(temp5);
    bound_init(temp3);
    bound_init(temp4);
    bound_init(temp6);
    bound_init(mibari);
    istempallocd = true; 
  }

  size_t ibarb, ia;
  size_t bj, baraj;
  size_t baraa = matpos(a^1, a);
  size_t bbarb = matpos(b, b^1);

  bool temp1infty = m->m[baraa] == 2;
  bool temp2infty = m->m[bbarb] == 2;

  bool temp3infty;
  bool temp4infty;
  
  bool temp5infty;
  bool temp6infty;
  
  bool iainfty;
  bool ibarbinfty;
  short mia_index;
  short mibarb_index;
  short mbj_index;
  short mbaraj_index;
  
  /* bool temp3infty, temp4infty; */
  
  for(size_t i=0; i<2*dim; i++) {
    ibarb = matpos2(i,b^1);
    ia = matpos2(i,a);


#if defined(FLOYDOPT)
    mibarb_index = m->m[ibarb];
    mia_index = m->m[ia];
    
    if(mibarb_index == 2) {
      if(mia_index == 2) {
	temp3infty = true;
	temp4infty = true;
      } else {
	temp3infty = false;
	temp4infty = false;
	myadd2(temp3, d, mia_index);
	myadd2(temp4, temp2, mia_index);
      }
    } else {
      temp3infty = false;
      temp4infty = false;
      myadd2(temp3, temp1, mibarb_index);
      myadd2(temp4, d, mibarb_index);

      if(mia_index != 2) {
	myadd2(temp5, d, mia_index);
	bound_bmin(temp3,temp5);
	myadd2(temp5, temp2, mia_index);
	bound_bmin(temp4,temp5);
      }
    }

    if(temp3infty && !temp4infty) {
      for(size_t j=0; j<=(i|1); j++) {
	baraj = matpos2(a^1,j);
	mbaraj_index = m->m[baraj];
	if(mbaraj_index != 2) {
	  myadd2(temp6, temp4, mbaraj_index);
	  size_t ij = matpos2(i,j);
	  if(bound_cmp(*getdbm(m,ij),temp6) > 0) {
	    setdbm(m,ij,temp6);
	  }
	}
      }
      // END
    } else if(!temp3infty && temp4infty) {
      for(size_t j=0; j<=(i|1); j++) {
	bj = matpos2(b,j);
	mbj_index = m->m[bj];
	if(mbj_index != 2) {
	  myadd2(temp5, temp3, mbj_index);
	  size_t ij = matpos2(i,j);
	  if(bound_cmp(*getdbm(m,ij),temp5) > 0) {
	    setdbm(m,ij,temp5);
	  }
	}
      }
      // END
    } else if(!temp3infty && !temp4infty) {

      for(size_t j=0; j<=(i|1); j++) {
	bj = matpos2(b,j);
	baraj = matpos2(a^1,j);

	mbj_index = m->m[bj];
	mbaraj_index = m->m[baraj];
      
	if(mbj_index == 2) {
	  temp5infty = true;
	} else {
	  temp5infty = false;
	  myadd2(temp5, temp3, mbj_index);
	}

	if(mbaraj_index == 2) {
	  temp6infty = true;
	} else {
	  temp6infty = false;
	  myadd2(temp6, temp4, mbaraj_index);
	}
      
	if(temp5infty) {
	  if(!temp6infty) {
	    size_t ij = matpos2(i,j);
	    if(bound_cmp(*getdbm(m,ij),temp6) > 0) {
	      setdbm(m,ij,temp6);
	    }
	  }
	} else {
	  if(!temp6infty) {
	    bound_bmin(temp5, temp6);
	  }

	  size_t ij = matpos2(i,j);
	  if(bound_cmp(*getdbm(m,ij),temp5) > 0) {
	    setdbm(m,ij,temp5);
	  }
	}
      }
      // END
    }
#else
    bound_add(temp5, d, *getdbm(m,ia));
    bound_add(temp3, temp1, *getdbm(m,ibarb));

    bound_bmin(temp3, temp5);

    bound_add(temp5, *getdbm(m,ibarb), d);
    bound_add(temp4, *getdbm(m,ia), temp2);
    bound_bmin(temp4,temp5);

    for(size_t j=0; j<=(i|1); j++) {
      bj = matpos2(b,j);
      baraj = matpos2(a^1,j);

      bound_add(temp5, temp3, *getdbm(m,bj));
      bound_add(temp6, temp4, *getdbm(m,baraj));
      bound_bmin(temp6, temp5);
      size_t ij = matpos2(i,j);
      if(bound_cmp(*getdbm(m,ij),temp6) > 0) {
	setdbm(m,ij,temp6);
      }
    }
#endif
  }
  
  return 0;
}

void strong_helper(dbm* m, size_t dim,  size_t a, size_t b, bound_t d, bound_t temp1, bound_t temp2){

  bound_t temp5; bound_init(temp5);
  for(size_t i=0; i<2*dim; i++) {
    
    bound_add(temp5, *getdbm(m,matpos2(i,a)) , d);
    bound_badd(temp5, *getdbm(m,matpos2(i,b^1)));
    
    size_t k = matpos(i,i^1);
    if(bound_cmp(*getdbm(m,k), temp5) > 0) {
      setdbm(m,k,temp5);
    }
  }

  bound_clear(temp5);
  return;
}
