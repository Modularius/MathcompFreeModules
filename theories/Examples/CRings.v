(******************************************************************************)
(**)
(******************************************************************************)
(* Let R : ringType and M : lmodType R                                        *)
(******************************************************************************)
(* R\lmod^n     ==                                                            *)
(* ringIBNType  == a record consisting of a ringType 'sort' and a proof that  *)
(*                 forall n m : nat,                                          *)
(*                  lmodIsomType R\lmod^n R\lmod^m -> n == m                  *)
(*                 R : ringIBN coerces to ringType                            *)
(* Every commutative ring satisfies the IBN condition so (R : comRingType)    *)
(* coerces to ringIBNType via cRingToRingIBN                                  *)
(* cRingToRingIBN R == given R : comRingType, this is a ringIBNType           *)
(******************************************************************************)
(* Let R : ringIBNType, and let M : fdFreeLmodType R                          *) 
(******************************************************************************)
(* steinitz_exchange M == proof that all bases of M have the same size        *)
(* invariant_dimension M == proof that all bases of M have the same size      *)
(* \dim(M) == the unique basis number of M                                    *)
(* dim_of_oplus == proof \dim(A \oplus B) = \dim(A) + \dim(B)                 *)
(* dim_of_bigoplus == proof \dim(\bigoplus_F I) = \sum_(f : F)\dim(I f)       *)
(* rank_nullity f == proof that \dim(A) = \dim(\ker(f)) + \dim(\im(f))        *)
(******************************************************************************)

From Coq.Logic Require Import ProofIrrelevance FunctionalExtensionality.
Require Import Coq.Init.Datatypes.
From mathcomp Require Import ssreflect ssrfun eqtype seq fintype finfun bigop matrix ring_quotient generic_quotient.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
  From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Modules Linears lmodLinearCombination DirectSum Basis FreeModules RingIBN.

Open Scope lmod_scope.
Open Scope ring_scope.

Section Result.
  Open Scope quotient_scope.
  Variable (R : comRingType) (I : {pred R})
  (idealI : idealr I) (kI : keyed_pred idealI).

  Definition qr := Quotient.rquot_ringType kI.

  Theorem ideal_IBN_implies_IBN : ringIBN.axiom qr -> ringIBN.axiom R.
  Proof. rewrite /ringIBN.axiom=>H n m psi.
  Admitted.
End Result.

Section Result.
  Variable (R : comRingType).
  Lemma cRingIBN : ringIBN.axiom R.
  Proof. move=>n m E.
  Admitted.
  Definition cRingToRingIBN : ringIBNType := ringIBN.Pack (ringIBN.Mixin cRingIBN).
End Result.

Coercion cRingToRingIBN : comRingType >-> type.
Notation cRingToRingIBN := cRingToRingIBN.

Close Scope ring_scope.
Close Scope lmod_scope.