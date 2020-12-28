(******************************************************************************)
(**)
(******************************************************************************)
(* Let R : ringType and A B C : lmodType R                                    *)
(* Let f : {linear A -> B} and g : {linear B -> C}                            *)
(******************************************************************************)
(* \1_A         == the linear identity : A -> A                               *)
(* linIDChain   == *)
(* \0_(A,B)     == the linear zero function : A -> B                          *)
(* linZeroChain == *)
(* g \oLin f    == the linear composition g \o f : {linear A -> C}            *)
(* linCompChain == *)
(******************************************************************************)
(* Let f g : {linear A -> B}                                                  *)
(******************************************************************************)
(* linear_eq == lemma rewriting equality of linear functions f = g            *)
(*              with equality of raw functions (f : A -> B) = g : A -> B      *)
(******************************************************************************)
(* linIsomType A B == a record consisting of:                                 *)
(*                1) functions isom_map : A -> B and isom_mapI : B -> A       *)
(*                2) linearity lemmas for isom_map and isom_mapI              *)
(*                3) cancellation lemmas proving isom_map and isom_mapI are   *)
(*                   inverses.                                                *)
(******************************************************************************)
(* Let f : linIsomType A B                                                    *)
(******************************************************************************)
(* isom_linmap f  == the linear map of type {linear A -> B} from isom_map f   *)
(* isom_linmapI f == the linear map of type {linear B -> A} from isom_mapI f  *)
(*  f             == coerces to isom_linmap f                                 *)
(* inv(f)         == isom_linmapI                                             *)
(* isomfK         ==  forall x : A, isom_map (isom_mapI x) = x                *)
(* isomKf         ==  forall x : B, isom_mapI (isom_map x) = x                *)
(* isomlK         ==  forall x : A, f (inv(f) x) = x                          *)
(* isomKl         ==  forall x : B, inv(f) (f x) = x                          *)
(* linIsomConcat  ==                                   *)


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
Require Import Modules.
Open Scope ring_scope.
Open Scope lmod_scope.


Module linID.
  Section Def.
    Variable (R : ringType) (M : lmodType R).
    Definition map : {linear M -> M} := locked (GRing.idfun_linear M).
    Lemma chain x : x = (map x).
    Proof. by rewrite /map -(lock). Qed.
  End Def.
End linID.
Notation "\id_ M " := (linID.map M) (at level 36, right associativity) : lmod_scope.
Notation linIDChain := (linID.chain).

Module linConcat.
  Section Def.
    Variable (R : ringType) (A B C : lmodType R)
    (f : {linear A -> B}) (g : {linear B -> C}).
    
    Definition map : {linear A -> C} := locked (GRing.comp_linear g f).
    Lemma chain x : g (f x) = (map x).
    Proof. by rewrite /map -(lock (GRing.comp_linear _ _)). Qed.
  End Def.
End linConcat.
Notation " g \oLin f " := (linConcat.map f g) (at level 36, right associativity) : lmod_scope.
Notation linCompChain := (linConcat.chain).


Module linZero.
  Section Def.
    Variable (R : ringType) (M1 M2 : lmodType R).

    Lemma lmod_zero_lin : linear (fun _ : M1 => @GRing.zero M2).
    Proof. by rewrite /(linear _)=>a x y; rewrite GRing.scaler0 GRing.addr0. Qed.

    Definition map : {linear M1 -> M2} := locked (Linear lmod_zero_lin).
    Lemma chain x : 0 = (map x).
    Proof. by rewrite /map -(lock). Qed.
  End Def.
End linZero.
Notation "\0_( M1 , M2 )" := (linZero.map M1 M2) (at level 36, right associativity) : lmod_scope.
Notation linZeroChain := (linZero.chain).

Section Results.
Variable (R : ringType) (M1 M2 : lmodType R).
Lemma linear_eq (p q : {linear M1 -> M2}) : p = q <-> (p : M1 -> M2) = (q : M1 -> M2).
Proof.
  split=>H.
  by inversion H.
  destruct p, q. simpl in H; destruct H.
  by rewrite (proof_irrelevance _ c c0).
Qed.
End Results.

Module linIsom.
  Section Def.
    Variable (R : ringType) (M1 M2 : lmodType R).
    Record mixin  (f : M1 -> M2)
                  (g : M2 -> M1)
   := Mixin {
      isom_lin : linear f;
      isom_inv_lin : linear g;
      isomfK : cancel f g;
      isomKf : cancel g f;
      }.
    Record type := Pack { isom_map : _ ; isom_mapI : _;
                          class_of : mixin isom_map isom_mapI;
                          isom_linmap : {linear M1 -> M2} := (Linear (isom_lin class_of));
                          isom_linmapI : {linear M2 -> M1} := (Linear (isom_inv_lin class_of));
    }.
    Definition Build (f : M1 -> M2)
                     (g : M2 -> M1)
                     (flin : linear f)
                     (glin : linear g)
                     (fg : cancel f g)
                     (gf : cancel g f)
                      := Pack (Mixin flin glin fg gf).

    Definition BuildPack (f : M1 -> M2) (g : M2 -> M1)
                      (fglin : linear f /\ linear g)
                      (fg_gf : cancel f g /\ cancel g f)
                      := Pack (@Mixin f g (proj1 fglin) (proj2 fglin) (proj1 fg_gf) (proj2 fg_gf)).

    Lemma isomlK (p : type) : cancel (isom_linmap p) (isom_linmapI p).
    Proof. rewrite /isom_linmap/isom_linmapI=>/=.
    apply (isomfK (class_of p)). Qed.
    
    Lemma isomKl (p : type) : cancel (isom_linmapI p) (isom_linmap p).
    Proof. rewrite /isom_linmap/isom_linmapI=>/=.
    apply (isomKf (class_of p)). Qed.
  End Def.

  Import GRing.
  Section Invert.
  Variable (R : ringType) (M1 M2 : lmodType R) (f : type M1 M2).
  Definition Invert : type M2 M1
     := @Build _ _ _
          (isom_linmapI f)
          (isom_linmap f)
          (linearPZ(isom_linmapI f)) (linearPZ (isom_linmap f))
          (isomKf (class_of f)) (isomfK (class_of f)).
  End Invert.
  Section Concat.
    Variable (R : ringType) (M1 M2 M3 : lmodType R).
    Variable (I1 : type M1 M2) (I2 : type M2 M3).
    Local Coercion class_of : type >-> mixin.
    Program Definition Concat : type M1 M3
     := @Build _ _ _
          (isom_linmap I2 \o isom_linmap I1)
          (isom_linmapI I1 \o isom_linmapI I2)
          (linearPZ (comp_linear (isom_linmap I2) (isom_linmap I1)))
          (linearPZ (comp_linear (isom_linmapI I1) (isom_linmapI I2)))
           _ _.
    Next Obligation.
    rewrite /isom_linmap/isom_linmapI=>/=.
    by rewrite/comp=>x; rewrite (isomfK I2) (isomfK I1).
    Qed. Next Obligation.
    rewrite /isom_linmap/isom_linmapI=>/=.
    by rewrite/comp=>x; rewrite (isomKf I1) (isomKf I2).
    Qed.
  End Concat.

  Section Results.
  Variable (R : ringType) (M1 M2 : lmodType R).
  Lemma concatKl (p : type M1 M2) : (isom_linmap p) \oLin (isom_linmapI p) = \id__.
  Proof. rewrite !linear_eq.
    apply functional_extensionality=>x.
    by rewrite -linCompChain (isomKl p) -linIDChain.
  Qed.
  Lemma concatlK (p : type M1 M2) : (isom_linmapI p) \oLin (isom_linmap p) = \id__.
  Proof. rewrite !linear_eq.
    apply functional_extensionality=>x.
    by rewrite -linCompChain (isomlK p) -linIDChain.
  Qed.
  End Results.
End linIsom.
Notation linIsomType := (linIsom.type).
Notation linIsomBuild := (linIsom.Build).
Notation linIsomBuildPack := (linIsom.BuildPack).
Notation linIsomConcat := (linIsom.Concat).
Notation linIsomInvert := (linIsom.Invert).
Notation isom_linmap := (linIsom.isom_linmap).
Notation isom_linmapI := (linIsom.isom_linmapI).
Notation isomfK := (linIsom.isomfK).
Notation isomKf := (linIsom.isomKf).
Notation isomlK := (linIsom.isomlK).
Notation isomKl := (linIsom.isomKl).
Notation isom_concatlK := (linIsom.concatlK).
Notation isom_concatKl := (linIsom.concatKl).
Coercion linIsom.class_of : linIsomType >-> linIsom.mixin.
Coercion linIsom.isom_linmap : linIsomType >-> GRing.Linear.map.
Notation "inv( f )" := (isom_linmapI f) (at level 36, right associativity) : lmod_scope.

Module BilinearMap.
Section Def.
    Variable (R : ringType) (M1 M2 N: lmodType R).
    Record mixin  (f : M1 -> M2 -> N)
   := Mixin {
      linear1 : forall m2, linear (f^~m2);
      linear2 : forall m1, linear (f m1);
      }.
    Record type := Pack { map : _ ; class_of : mixin map; }.
    Definition bilinear (f : M1 -> M2 -> N) := (forall m2, linear (f^~m2)) /\ (forall m1, linear (f m1)).

    Definition Build (f : M1 -> M2 -> N) (blin : bilinear f)
      := Pack (@Mixin f (proj1 blin) (proj2 blin)).

    Definition FixSecond (f : type) (m2 : M2) : {linear M1 -> N}
     := Linear (linear1 (class_of f) m2).
    Definition FixFirst (f : type) (m1 : M1) : {linear M2 -> N}
     := Linear (linear2 (class_of f) m1).
  End Def.
End BilinearMap.

Notation "\bilinFix1_ m1 ( f )" := (BilinearMap.FixFirst f m1) (at level 36, right associativity) : lmod_scope.
Notation "\bilinFix2_ m2 ( f )" := (BilinearMap.FixSecond f m2) (at level 36, right associativity) : lmod_scope.
Notation "\bilinear( M1 -> M2 -> N )" := (BilinearMap.type M1 M2 N) (at level 36, right associativity).
Coercion BilinearMap.class_of : BilinearMap.type >-> BilinearMap.mixin.
Coercion BilinearMap.map : BilinearMap.type >-> Funclass.


Close Scope ring_scope.
Close Scope lmod_scope.
