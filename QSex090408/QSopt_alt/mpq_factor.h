/****************************************************************************/
/*                                                                          */
/*  This file is part of QSopt_ex.                                          */
/*                                                                          */
/*  (c) Copyright 2006 by David Applegate, William Cook, Sanjeeb Dash,      */
/*  and Daniel Espinoza                                                     */
/*                                                                          */
/*  This code may be used under the terms of the GNU General Public License */
/*  (Version 2.1 or later) as published by the Free Software Foundation.    */
/*                                                                          */
/*  Alternatively, use is granted for research purposes only.               */ 
/*                                                                          */
/*  It is your choice of which of these two licenses you are operating      */
/*  under.                                                                  */
/*                                                                          */
/*  We make no guarantees about the correctness or usefulness of this code. */
/*                                                                          */
/****************************************************************************/

/* RCSINFO $Id: mpq_factor.h,v 1.3 2003/11/05 16:57:39 meven Exp $ */
#ifndef mpq___QS_FACTOR_H_
#define mpq___QS_FACTOR_H_
#include "basicdefs.h"
#include "econfig.h"
#include "mpq_dstruct.h"

typedef char mpq_QSbool;

typedef struct mpq_uc_info
{
	int cbeg;
	int nzcnt;
	int next;
	int prev;
	int delay;
}
mpq_uc_info;

typedef struct mpq_ur_info
{
	mpq_t max;
	int rbeg;
	int nzcnt;
	int pivcnt;
	int next;
	int prev;
	int delay;
}
mpq_ur_info;

typedef struct mpq_lc_info
{
	int cbeg;
	int nzcnt;
	int c;
	int crank;
	int delay;
}
mpq_lc_info;

typedef struct mpq_lr_info
{
	int rbeg;
	int nzcnt;
	int r;
	int rrank;
	int delay;
}
mpq_lr_info;

typedef struct mpq_er_info
{
	int rbeg;
	int nzcnt;
	int r;
}
mpq_er_info;

typedef struct mpq_factor_work
{
	int max_k;
	mpq_t fzero_tol;
	mpq_t szero_tol;
	mpq_t partial_tol;
	double ur_space_mul;
	double uc_space_mul;
	double lc_space_mul;
	double lr_space_mul;
	double er_space_mul;
	double grow_mul;
	int p;
	int etamax;
	double minmult;
	double maxmult;
	double updmaxmult;
	double dense_fract;
	int dense_min;

	mpq_t maxelem_orig;
	int nzcnt_orig;
	mpq_t maxelem_factor;
	int nzcnt_factor;
	mpq_t maxelem_cur;
	int nzcnt_cur;

	mpq_t partial_cur;

	int dim;
	int stage;
	int nstages;
	int etacnt;
	mpq_t *work_coef;
	int *work_indx;
	mpq_uc_info *uc_inf;
	mpq_ur_info *ur_inf;
	mpq_lc_info *lc_inf;
	mpq_lr_info *lr_inf;
	mpq_er_info *er_inf;
	int *ucindx;									/* row index for column data */
	int *ucrind;									/* index of column in row data */
	mpq_t *uccoef;						/* coefficient for column data */
	int *urindx;									/* col index for row data */
	int *urcind;									/* index of row in column data */
	mpq_t *urcoef;						/* coefficient for row data */
	int *lcindx;									/* row index for L data */
	mpq_t *lccoef;						/* coefficient for L row data */
	int *lrindx;									/* col index for L data */
	mpq_t *lrcoef;						/* coefficient for L col data */
	int *erindx;									/* col index for eta data */
	mpq_t *ercoef;						/* coefficient for eta data */
	int *rperm;
	int *rrank;
	int *cperm;
	int *crank;
	mpq_svector xtmp;
	int ur_freebeg;
	int ur_space;
	int uc_freebeg;
	int uc_space;
	int lc_freebeg;
	int lc_space;
	int lr_freebeg;
	int lr_space;
	int er_freebeg;
	int er_space;

	int *p_nsing;
	int **p_singr;
	int **p_singc;

	mpq_t *dmat;
	int drows;
	int dcols;
	int dense_base;
}
mpq_factor_work;

void mpq_ILLfactor_init_factor_work (mpq_factor_work * f),
  mpq_ILLfactor_free_factor_work (mpq_factor_work * f),
  mpq_ILLfactor_ftran (mpq_factor_work * f,
									 mpq_svector * a,
									 mpq_svector * x),
  mpq_ILLfactor_ftran_update (mpq_factor_work * f,
													mpq_svector * a,
													mpq_svector * upd,
													mpq_svector * x),
  mpq_ILLfactor_btran (mpq_factor_work * f,
									 mpq_svector * a,
									 mpq_svector * x);

int mpq_ILLfactor_create_factor_work (mpq_factor_work * f,
																	int dim),
  mpq_ILLfactor_set_factor_iparam (mpq_factor_work * f,
															 int param,
															 int val),
  mpq_ILLfactor_set_factor_dparam (mpq_factor_work * f,
															 int param,
															 mpq_t val),
  mpq_ILLfactor (mpq_factor_work * f,
						 int *basis,
						 int *cbeg,
						 int *clen,
						 int *cindx,
						 mpq_t * ccoef,
						 int *p_nsing,
						 int **p_singr,
						 int **p_singc),
  mpq_ILLfactor_update (mpq_factor_work * f,
										mpq_svector * a,
										int col,
										int *p_refact);

#endif /* mpq___QS_FACTOR_H_ */
