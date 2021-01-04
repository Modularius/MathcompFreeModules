(******************************************************************************)
(* Dr Daniel Kirk (c) 2021                                                    *)
(******************************************************************************)
(* ringIBN.axiom R == for a ring R, a proposition that:                       *)
(*                    forall n m : nat,                                       *)
(*                       lmodIsomType R\lmod^n R\lmod^m -> n == m             *)
(* ringIBNType     == a record consisting of a ringType 'sort' and a proof    *)
(*                    that (ringIBN.axiom sort holds).                        *)
(*                    R : ringIBN coerces to ringType                         *)
(******************************************************************************)
(* IBN_equiv_equal_basis_nums == proof that all bases of M have the same size *)
(******************************************************************************)
(* Let R : ringIBNType, and let A, B : fdFreeLmodType R                       *)
(******************************************************************************)
(* \dim(A)         == the unique basis number of M                            *)
(* dim_of_oplus    == proof that \dim(A \oplus B) = \dim(A) + \dim(B)         *)
(******************************************************************************)
(* Let I : linIsomType A B                                                    *)
(******************************************************************************)
(* dim_of_isom I   == proof that \dim(A) = \dim(B)                            *)
(******************************************************************************)
(* Let F : finType and I : F -> fdFreeLmodType R                              *)
(******************************************************************************)
(* dim_of_bigoplus == proof that \dim(\bigoplus_F I) = \sum_(f : F)\dim(I f)  *)
(******************************************************************************)

From Coq.Logic Require Import ProofIrrelevance FunctionalExtensionality.
Require Import Coq.Init.Datatypes.
From mathcomp Require Import ssreflect ssrfun eqtype seq fintype bigop.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
  From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Modules Linears lmodLC DirectSum Basis FreeModules.

Open Scope lmod_scope.
Open Scope ring_scope.
Module ringIBN.
  Section Def.
    Definition axiom (R : ringType) :=
      forall n m : nat,
        (linIsomType (R\lmod^n) (R\lmod^m)) -> n == m.

    Record mixin (R : ringType) := Mixin { _ : axiom R; }.
    Record type := Pack { sort : _;  class_of : mixin sort; }.
  End Def.
  Section Result.
    Variable (R : ringType).
    Theorem IBN_equiv_equal_basis_nums : axiom R <->
      forall (M : fdFreeLmodType R) (B1 B2 : lmodFinBasisType M),
      (basis_number B1) == (basis_number B2).
    Proof.
      split; rewrite/axiom=>H.
        move=>M B1 B2.
        move: (H (basis_number B1) (basis_number B2))=>H2.
        have N1 : (basis_number B1) = size (enum (to_FinType (fdBasis (fdFreeLmodPack B1)))) by rewrite -cardT.
        have N2 : (basis_number B2) = size (enum (to_FinType (fdBasis (fdFreeLmodPack B2)))) by rewrite -cardT.
        apply (H _ _ (linIsomConcat (linIsomInvert (freeLinear.to_row N1)) (freeLinear.to_row N2))).

        move=>n m f.
        move: (H (fdFreeLmod_vector R m)
          (fdBasis (fdFreeLmod_vector R m))
          (@lmodBasis_to_finLmodBasis _ _
            (lmodBasis.isomorphicBasis f (lmodFinBasis_to_lmodBasis (fdBasis (fdFreeLmod_vector R n))))
            (Finite.class (ordinal_finType n))
          )).
      by rewrite /basis_number card_ord card_ord eq_sym.
    Qed.
  End Result.

  Module Exports.
    Notation "'\' 'dim' '(' M ')'" := (basis_number (fdBasis M)) (at level 0, format "'\' 'dim' '(' M ')'") : lmod_scope.
    Notation ringIBNType := type.
    Coercion sort : type >-> ringType.
    Coercion class_of : type >-> mixin.
  End Exports.

  Section Results.
    Variable (R : type).
    Export Exports.
    Open Scope nat_scope.
    Lemma dim_of_oplus : forall (M1 M2 : fdFreeLmodType R),
    \dim(M1 \foplus M2) = \dim(M1) + \dim(M2).
    Proof. move=> M1 M2.
      by rewrite /dsFdFreeLmod.Pair.fdFreeLmod/lmodFinBasis.basis_number card_sum.
    Qed.

    Lemma dim_of_bigoplus : forall {F : finType} (I : F -> fdFreeLmodType R),
      \dim(\fbigoplus I) = \sum_f (\dim(I f)).
    Proof. move => F I.
      rewrite /dsFdFreeLmod.type/dsFdFreeLmod.Seq.fdFreeLmod -big_enum enumT =>/=.
      induction(Finite.enum F); by [
      rewrite /lmodFinBasis.basis_number big_nil card_void|
      rewrite big_cons -IHl -dim_of_oplus /dsFdFreeLmod.Pair.fdFreeLmod/dsFdFreeLmod.Seq.basis].
    Qed.

    Lemma dim_of_isom : forall (M1 M2 : fdFreeLmodType R) (I : linIsomType M1 M2),
      \dim(M1) = \dim(M2).
    Proof. move=>M1 M2 I.
      move:(linIsom.Concat (linIsom.Concat (linIsom.Invert (freeLinear.to_row (fdFreeLmod.erefl M1))) I) (freeLinear.to_row (fdFreeLmod.erefl M2)))=>II.
      destruct R as [R' [A]].
      move:(A _ _ II)=>B; move/eqP in B.
      by rewrite /basis_number !cardT.
    Qed.


    Close Scope nat_scope.
  End Results.
End ringIBN.
Export ringIBN.Exports.

Close Scope ring_scope.
Close Scope lmod_scope.