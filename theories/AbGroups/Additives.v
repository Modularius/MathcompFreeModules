(******************************************************************************)
(**)
(******************************************************************************)
(* Let A B C : lmodType                                    *)
(* Let f : {additive A -> B} and g : {additive B -> C}                        *)
(******************************************************************************)
(* \1_A         == the additive identity : A -> A                             *)
(* addIDChain   == *)
(* \0_(A,B)     == the additive zero function : A -> B                        *)
(* addZeroChain == *)
(* g \oAdd f    == the additive composition g \o f : {additive A -> C}        *)
(* addCompChain == *)
(******************************************************************************)
(* Let f g : {additive A -> B}                                                *)
(******************************************************************************)
(* additive_eq == lemma rewriting equality of additive functions f = g        *)
(*              with equality of raw functions (f : A -> B) = g : A -> B      *)
(******************************************************************************)
(* addIsomType A B == a record consisting of:                                 *)
(*                1) functions isom_map : A -> B and isom_mapI : B -> A       *)
(*                2) additivity lemmas for isom_map and isom_mapI             *)
(*                3) cancellation lemmas proving isom_map and isom_mapI are   *)
(*                   inverses.                                                *)
(******************************************************************************)
(* Let f : addIsomType A B                                                    *)
(******************************************************************************)
(* isom_addmap f  == the map of type {additive A -> B} from isom_map f        *)
(* isom_addmapI f == the map of type {additive B -> A} from isom_mapI f       *)
(*  f             == coerces to isom_addmap f                                 *)
(* inv(f)         == isom_addmapI                                             *)
(* isomfK         ==  forall x : A, isom_map (isom_mapI x) = x                *)
(* isomKf         ==  forall x : B, isom_mapI (isom_map x) = x                *)
(* isomaK         ==  forall x : A, f (inv(f) x) = x                          *)
(* isomKa         ==  forall x : B, inv(f) (f x) = x                          *)
(* addIsomConcat  ==                                   *)


Require Import Coq.Program.Tactics.
From Coq.Logic Require Import ProofIrrelevance FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun.
From mathcomp Require Import eqtype choice.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.
Require Import AbGroups.
Open Scope ring_scope.
Open Scope zmod_scope.


Module addID.
  Section Def.
    Variable (M : zmodType).
    Definition map : {additive M -> M} := locked (GRing.idfun_additive M).
    Lemma chain x : x = (map x).
    Proof. by rewrite /map -(lock). Qed.
  End Def.
End addID.
Notation "\id_ M " := (addID.map M) (at level 36, right associativity) : zmod_scope.
Notation addIDChain := (addID.chain).

Module addConcat.
  Section Def.
    Variable (A B C : zmodType)
    (f : {additive A -> B}) (g : {additive B -> C}).
    
    Definition map : {additive A -> C} := locked (GRing.comp_additive g f).
    Lemma chain x : g (f x) = (map x).
    Proof. by rewrite /map -(lock (GRing.comp_additive _ _)). Qed.
  End Def.
End addConcat.
Notation " g \oAdd f " := (addConcat.map f g) (at level 36, right associativity) : zmod_scope.
Notation addCompChain := (addConcat.chain).


Module addZero.
  Section Def.
    Variable (M1 M2 : zmodType).

    Lemma zmod_zero_add : additive (fun _ : M1 => @GRing.zero M2).
    Proof. by move=>x y; rewrite GRing.subr0. Qed.

    Definition map : {additive M1 -> M2} := locked (Additive zmod_zero_add).
    Lemma chain x : 0 = (map x).
    Proof. by rewrite /map -(lock). Qed.
  End Def.
End addZero.
Notation "\0_( M1 , M2 )" := (addZero.map M1 M2) (at level 36, right associativity) : zmod_scope.
Notation addZeroChain := (addZero.chain).

Section Results.
Variable (M1 M2 : zmodType).
Lemma additive_eq (p q : {additive M1 -> M2}) : p = q <-> (p : M1 -> M2) = (q : M1 -> M2).
Proof.
  split=>H.
  by inversion H.
  destruct p, q. simpl in H; destruct H.
  by rewrite (proof_irrelevance _ a a0).
Qed.
End Results.

Module addIsom.
  Section Def.
    Variable (M1 M2 : zmodType).
    Record mixin  (f : M1 -> M2)
                  (g : M2 -> M1)
   := Mixin {
      isom_add : additive f;
      isom_inv_add : additive g;
      isomfK : cancel f g;
      isomKf : cancel g f;
      }.
    Record type := Pack { isom_map : _ ; isom_mapI : _;
                          class_of : mixin isom_map isom_mapI;
                          isom_addmap : {additive M1 -> M2} := (Additive (isom_add class_of));
                          isom_addmapI : {additive M2 -> M1} := (Additive (isom_inv_add class_of));
    }.
    Definition Build (f : M1 -> M2)
                     (g : M2 -> M1)
                     (fadd : additive f)
                     (gadd : additive g)
                     (fg : cancel f g)
                     (gf : cancel g f)
                      := Pack (Mixin fadd gadd fg gf).

    Definition BuildPack (f : M1 -> M2) (g : M2 -> M1)
                      (fgadd : additive f /\ additive g)
                      (fg_gf : cancel f g /\ cancel g f)
                      := Pack (@Mixin f g (proj1 fgadd) (proj2 fgadd) (proj1 fg_gf) (proj2 fg_gf)).

    Lemma isomaK (p : type) : cancel (isom_addmap p) (isom_addmapI p).
    Proof. rewrite /isom_addmap/isom_addmapI=>/=.
    apply (isomfK (class_of p)). Qed.
    
    Lemma isomKa (p : type) : cancel (isom_addmapI p) (isom_addmap p).
    Proof. rewrite /isom_addmap/isom_addmapI=>/=.
    apply (isomKf (class_of p)). Qed.
  End Def.

  Import GRing.
  Section Invert.
  Variable (M1 M2 : zmodType) (f : type M1 M2).
  Definition Invert : type M2 M1
     := @Build _ _
          (isom_addmapI f)
          (isom_addmap f)
          (isom_inv_add (class_of f)) (isom_add (class_of f))
          (isomKf (class_of f)) (isomfK (class_of f)).
  End Invert.
  Section Concat.
    Variable (M1 M2 M3 : zmodType).
    Variable (I1 : type M1 M2) (I2 : type M2 M3).
    Local Coercion class_of : type >-> mixin.
    Program Definition Concat : type M1 M3
     := @Build _ _
          (isom_addmap I2 \o isom_addmap I1)
          (isom_addmapI I1 \o isom_addmapI I2)
          (comp_is_additive (isom_addmap I2) (isom_addmap I1))
          (comp_is_additive (isom_addmapI I1) (isom_addmapI I2))
           _ _.
    Next Obligation.
    rewrite /isom_addmap/isom_addmapI=>/=.
    by rewrite/comp=>x; rewrite (isomfK I2) (isomfK I1).
    Qed. Next Obligation.
    rewrite /isom_addmap/isom_addmapI=>/=.
    by rewrite/comp=>x; rewrite (isomKf I1) (isomKf I2).
    Qed.
  End Concat.

  Section Results.
  Variable (M1 M2 : zmodType).
  Lemma concatKa (p : type M1 M2) : (isom_addmap p) \oAdd (isom_addmapI p) = \id__.
  Proof. rewrite !additive_eq.
    apply functional_extensionality=>x.
    by rewrite -addCompChain (isomKa p) -addIDChain.
  Qed.
  Lemma concataK (p : type M1 M2) : (isom_addmapI p) \oAdd (isom_addmap p) = \id__.
  Proof. rewrite !additive_eq.
    apply functional_extensionality=>x.
    by rewrite -addCompChain (isomaK p) -addIDChain.
  Qed.
  End Results.
End addIsom.
Notation addIsomType := (addIsom.type).
Notation addIsomBuild := (addIsom.Build).
Notation addIsomBuildPack := (addIsom.BuildPack).
Notation addIsomConcat := (addIsom.Concat).
Notation addIsomInvert := (addIsom.Invert).
Notation isom_addmap := (addIsom.isom_addmap).
Notation isom_addmapI := (addIsom.isom_addmapI).
Notation isomfK := (addIsom.isomfK).
Notation isomKf := (addIsom.isomKf).
Notation isomaK := (addIsom.isomaK).
Notation isomKa := (addIsom.isomKa).
Notation isom_concataK := (addIsom.concataK).
Notation isom_concatKa := (addIsom.concatKa).
Coercion addIsom.class_of : addIsomType >-> addIsom.mixin.
Coercion addIsom.isom_addmap : addIsomType >-> GRing.Additive.map.
Notation "inv( f )" := (isom_addmapI f) (at level 36, right associativity) : zmod_scope.


Close Scope ring_scope.
Close Scope zmod_scope.
