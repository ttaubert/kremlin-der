/* This file was auto-generated by KreMLin! */
#ifndef __FStar_H
#define __FStar_H


#include "Test.h"
#include "kremlib.h"

typedef void *FStar_Pervasives_ex_pre;

typedef void *FStar_Set_eqtype;

extern void FStar_PropositionalExtensionality_axiom();

typedef struct 
{
  void *t;
  void **b;
}
FStar_Buffer_abuffer;

extern bool FStar_Buffer_arefs(Prims_prop *x0(FStar_Buffer_abuffer x0), Prims_nat x1);

extern Prims_int FStar_Int_logand(Prims_pos x0, Prims_int x1, Prims_int x2);

extern Prims_int FStar_Int_logxor(Prims_pos x0, Prims_int x1, Prims_int x2);

extern Prims_int FStar_Int_logor(Prims_pos x0, Prims_int x1, Prims_int x2);

extern Prims_int FStar_Int_lognot(Prims_pos x0, Prims_int x1);

extern Prims_int FStar_Int_shift_right(Prims_pos x0, Prims_int x1, Prims_nat x2);
#endif
