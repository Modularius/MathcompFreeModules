(* math-algebra (c) 2020 Dr Daniel Kirk                                       *)
(******************************************************************************)
(* Let R : ringType                                                           *)
(******************************************************************************)
(* freeLmodType R == a record consisting of an lmodType R 'sort' and          *)
(*                   a (lmodBasisType sort)                                   *)
(*                   M : freeLmodType M coerces to its underlying lmodType    *)
(******************************************************************************)
(* Let M : freeLmodType R                                                     *)
(* basis M             == underlying lmodBasisType object of M                *)
(* \freeBasisCoef_(b) x == \basisProj_b^(basis M) x                           *)
(******************************************************************************)
(* fdFreeLmodType R == a record consisting of an lmodType R 'sort' and        *)
(*                     a (lmodFinBasisType sort)                              *)
(*                     M : fdFreeLmodType M coerces to its underlying         *)
(*                     lmodType but not to freeLmodType                       *)
(******************************************************************************)
(* Let M : fdFreeLmodType R                                                   *)
(*                fdBasis M == underlying lmodFinBasisType object of M        *)
(* fdFreeLmod_to_freeLmod M == converts to underlying lmodBasisType           *)
(*   \fdFreeBasisCoef_(b) x == \finBasisProj_b^(fdBasis M) x                  *)
(******************************************************************************)
(* null_fdFreeLmod R == the fdFreeLmodType structure for null_lmodType:       *)
(*                        the trivial module over R. It has the null basis.   *)
(* unit_fdFreeLmod R == the fdFreeLmodType structure for unit_lmodType:       *)
(*                        R as a module over itself. It has a basis with one  *)
(*                        element (unit).                                     *)
(* matrix_fdFreeLmod R n m == the fdFreeLmodType structure for                *)
(*                            matrix_lmodType n m: the matrix objects defined *)
(*                            in mathcomp matrix.v. It has a basis 'I_n*'I_m  *)
(* vector_fdFreeLmod R n   == the fdFreeLmodType structure for                *)
(*                            matrix_lmodType 1 n, the row matrix objects.    *)
(*                            It has a basis 'I_n                             *)
(* poly_fdFreeLmod R n     == the fdFreeLmodType structure for                *)
(*                            poly_lmodType n.                                *)
(******************************************************************************)
(*        M1 \foplus M2  == the fdFreeLmodType given by M1 \oplus M2 and      *)
(*                          Pair.basis M1 M2                                  *)
(*                          Pair.basis M1 M2 == finBasisType with index-set   *)
(*                          (fdBasis M1) + (fdBasis M2) and                   *)
(*                          elem x := match x with                            *)
(*                            |inl y => (B1 y, 0)                             *)
(*                            |inr y => (0, B2 y)                             *)
(*                          end                                               *)
(* \fbigoplus_(f in L) I == the fdFreeLmodType given by \bigoplus_(f in L) I  *)
(*                          and Seq.basis I L                                 *)
(*                          Seq.basis I nil has                               *)
(*                            index-set == null_finType                       *)
(*                            elem x    == tt                                 *)
(*                          Seq.basis I a::L has                              *)
(*                            index-set ==                                    *)
(*                              Pair.basis (fdBasis (I a)) (Seq.basis I L)    *)
(*                            elem x    ==  match x with                      *)
(*                                          |inl y => (fdBasis (I a) y, 0)    *)
(*                                          |inr y => (0, Seq.basis I L y)    *)
(*                                          end                               *)
(*       \fbigoplus_F I == equivalent to \fbigoplus_(f : F) I                 *)
(*         \fbigoplus I == equivalent to \fbigoplus_(f : F) I                 *)
(*                         where I : F -> lmodType R                          *)
(******************************************************************************)
(* FreeModule_UniversalProperty == *)
(******************************************************************************)

Require Import Coq.Program.Tactics.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun seq.
From mathcomp Require Import eqtype fintype bigop finfun matrix.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import Modules Linears DirectSum FiniteSupport lmodLC Basis.
Set Implicit Arguments.
Unset Strict Implicit.
Open Scope ring_scope.

Include GRing.

Open Scope lmod_scope.
(*
  Definitions of the Free and Finite Dimensional Free Module Types
    *)

Module freeLmod.
  Section Def.
    Variable (R : ringType).
    Record mixin (M : lmodType R) := Mixin { basis : lmodBasisType M; }.
    Record type := Pack { sort : _ ;  class_of : mixin sort; }.
    Definition Build {M : lmodType R} (B : lmodBasisType M) := Pack (Mixin B).
  End Def.

  Module Exports.
    Coercion sort : type >-> lmodType.
    Coercion class_of : type >-> mixin.
    Notation freeLmodType := type.
    Notation basis := basis.
    Notation freeLmodPack := Build.
    Notation coef := (fun (R : ringType) (M : type R) b => \basisProj_b^(basis M)).
    Notation "\freeBasisCoef_( b ) x" := (@coef _ _ b x) (at level 36) : lmod_scope.
  End Exports.
End freeLmod.
Export freeLmod.Exports.

(* Finite dimenisonal free modules are compatible with finite direct sums
   That is they can be built-up and have corresponding proj and inj morphisms *)
Module fdFreeLmod.
  Section Def.
    Variable (R : ringType).
    Record mixin (M : lmodType R) := Mixin { fdBasis : lmodFinBasis.type M; }.
    Record type := Pack { sort : _ ;  class_of : mixin sort; }.
    Definition Build {M : lmodType R} (B : lmodFinBasis.type M) := Pack (Mixin B).

    Definition to_arb (F : type) := freeLmod.Build (lmodFinBasis.to_lmodBasis (fdBasis (class_of F))).
  End Def.


  Module Exports.
    Coercion sort : type >-> lmodType.
    Coercion class_of : type >-> mixin.
    Notation fdFreeLmodType := type.
    Notation fdBasis := fdBasis.
    Notation fdFreeLmodPack := Build.

    Notation coef := (fun (R : ringType) (M : type R) b => \basisProj_b^(fdBasis M)).
    Notation "\fdFreeBasisCoef_( b ) x" := (@coef _ _ b x) (at level 36) : lmod_scope.
    Notation fdFreeLmod_to_freeLmod := to_arb.
  End Exports.
End fdFreeLmod.
Export fdFreeLmod.Exports.



(*
  Free Module Types of:
    the trivial modules (null basis)
    the ring as a module over itself (unit basis)
    matrix modules over a ring
    polynomial modules over a ring
    *)

Module fdFreeLmodNull.
  Section Def.
    Variable (R : ringType).
    
    Definition nullBasis_fn := fun x : void => match x with end : (lmodZeroType R).

    Lemma null_injective : injective nullBasis_fn.
    Proof. by move=>x; destruct x. Qed.

    Lemma null_nondeg : non_degenerate nullBasis_fn.
    Proof. by move=>x; destruct x. Qed.

    Definition null_set := lmodFinSet.Build null_injective null_nondeg.

    Lemma null_li : lmodBasis.li null_set.
    Proof. move=>C H.
      rewrite lmodLC.eqFSFun/=.
      apply functional_extensionality=>b.
      destruct C as [coef [s [U E]]].
      by induction s.
    Qed.
    
    Lemma null_sp : lmodBasis.span null_set.
    Proof. move=>m;
      apply (exist _ (nullFSType R null_set) (lmodLC.null_sumsTo _)).
    Qed.
    Definition basis := lmodFinBasis.Build null_li null_sp.
  End Def.
  Module Exports.
    Canonical null_fdFreeLmod (R : ringType) := Eval hnf in @fdFreeLmodPack R _ (fdFreeLmodNull.basis R).
  End Exports.
End fdFreeLmodNull.
Export fdFreeLmodNull.Exports.





Module freeRingModule.
  Section Def.
    Variable (R : ringType).
    Definition fn := fun _ : unit_eqType => (GRing.one R) : (ringModType R).
    Lemma fn_injective : injective fn.
      Proof. by move=>x y; destruct x, y. Qed.
    Lemma fn_nondegen : non_degenerate fn.
      Proof. rewrite /fn=>x; apply GRing.oner_neq0. Qed.

    Definition bset := lmodFinSet.Build fn_injective fn_nondegen.

    Lemma bset_li : lmodBasis.li bset.
    Proof. move=>/=C S.
      rewrite lmodLC.eqFSFun/=.
      apply functional_extensionality=>/=b.
      destruct S as [s [U [H S]]]; move: s U H S.
      rewrite /bset/==>s U H S.
      case(C b == 0) as []eqn:E.
        by move/eqP in E.
        
        move/negbT in E.
        destruct s; [by move:(H _ E); rewrite in_nil|destruct s=>//].
          rewrite big_seq1/fn/(scale _)/= mulr1 in S; move/eqP in S;
          by destruct b, u.
    Qed.

    Lemma bset_spanning : lmodBasis.span bset.
    Proof. move=>x.
      refine (exist _ (unitFSType (B:= bset) tt x) _).
      move: (lmodLC.unit_sumsTo (B:=bset) tt x).
      by rewrite /scale/= mulr1.
    Qed.

    Definition basis : lmodFinBasisType (ringModType R) := lmodFinBasis.Build bset_li bset_spanning.
  End Def.
  Module Exports.
    Canonical unit_fdFreeLmod (R : ringType) := Eval hnf in @fdFreeLmodPack R (ringModType R) (freeRingModule.basis R).
  End Exports.
End freeRingModule.
Export freeRingModule.Exports.

Module freeLmodMatrix.
  Section Def.
    Variable (R : ringType) (m n : nat).
    Definition fn pp := @delta_mx R m n pp.1 pp.2.
    Lemma fn_injective : injective fn.
      Proof. rewrite/fn=>x y; rewrite /delta_mx -matrixP/eqrel=>H.
        assert(H := H y.1 y.2); move: H;
        rewrite !mxE !eq_refl/==>H.
        have: (y.1 == x.1) by 
          case(y.1 == x.1) as []eqn:E=>//; move: H;
          rewrite !E !(rwP eqP) eq_sym oner_eq0.
        have: (y.2 == x.2) by
          case(y.2 == x.2) as []eqn:E=>//; move: H;
          rewrite E andbC !(rwP eqP) eq_sym oner_eq0.
        destruct x, y; rewrite -!(rwP eqP)=>/=H1 H2.
        by rewrite H1 H2.
      Qed.

      Lemma fn_nondegen : non_degenerate fn.
      Proof. rewrite /fn=>x; rewrite /delta_mx -(rwP negP)-(rwP eqP)-matrixP=>H.
        assert(H := H x.1 x.2); move: H.
        by rewrite !mxE !eq_refl (rwP eqP) oner_eq0.
      Qed.

      Definition fn_bset := lmodFinSet.Build fn_injective fn_nondegen.

      Lemma big_or (T : finType) (M : zmodType) (F : T -> M)  P1 P2 : \sum_(i | P1 i || P2 i)F i = \sum_(i | P1 i)F i + \sum_(i |P2 i)F i - \sum_(i | P1 i && P2 i)F i.
      Proof.
        rewrite !big_mkcond !(big_mkcond P1) !(big_mkcond P2) !(big_mkcond (fun i => P1 i && P2 i)) -!big_enum-!big_mkcond.
        induction (enum _).
        by rewrite !big_nil subr0 addr0.
        rewrite !big_cons.
        case(P1 a) as []eqn:E1.
        case(P2 a) as []eqn:E2=>/=.
        rewrite (addrC _ (\sum_(j <- _| P2 j) _)) !addrA.
        by rewrite addrKA IHl !addrA/=.
        by rewrite IHl/= !addrA.
        case(P2 a) as []eqn:E2=>/=.
        rewrite !addrA (addrC (\sum_(j <- _| P1 j) _) _).
        by rewrite IHl !addrA/=.
        by rewrite IHl.
      Qed.

      Lemma seq_basis (c : 'I_m*'I_n -> R) (x : seq ('I_m*'I_n)) (U : uniq x) : \sum_(b <- x) c b *: delta_mx b.1 b.2 =  \sum_(i < m) \sum_(j < n) (if(i,j) \in x then c (i,j) else 0) *: delta_mx i j.
      Proof.
        rewrite pair_big.
        symmetry; under eq_bigr do rewrite (lmod_ifthenelse_sum (fun p => c p) (fun p => delta_mx p.1 p.2) (fun p => p \in x)); symmetry.
        simpl fst; simpl snd.
        rewrite -big_mkcond/=.
        induction x.
        rewrite big_nil.
        under eq_bigl do rewrite in_nil.
        by rewrite big_pred0.

        rewrite big_cons.
        simpl in U; move/andP in U.
        rewrite (IHx (proj2 U)).
        symmetry; under eq_bigl do rewrite in_cons;symmetry.
        rewrite big_or -(IHx (proj2 U)) (big_pred1 a).
        destruct a=>/=.
        rewrite (big_mkcond (fun _ => _ && (_ \in _)))=>/=.
        rewrite (big1 _ _ (fun i => if _ then _ else _)).
        by rewrite subr0.
        move=>i _.
        case((i.1, i.2) == (o, o0)) as []eqn:E1.
        case((i.1, i.2) \in x) as []eqn:E2.
        move/eqP in E1.
        by rewrite -E1 E2/= in U; destruct U.
        by rewrite E2/=.
        by [].
        move=>i; destruct a.
        by rewrite/pred1/=.
      Qed.
(*
        Lemma sum_sdgsdg P1 P2 : \sum_i
        (if (P1 i || P2 i) then F i else 0) *: delta_mx i i0
         induction x=>c.
        rewrite big_nil.
        under eq_bigr do under eq_bigr do rewrite in_nil.
        rewrite {1}(matrix_sum_delta 0)/=.
        by under eq_bigr do under eq_bigr do rewrite mxE.

        rewrite big_cons.
        simpl in U; move/andP in U.
        rewrite (IHx (proj2 U)).
        symmetry; under eq_bigr do under eq_bigr do rewrite in_cons; symmetry.

        clear IHx. induction m. by destruct a as [o oo]; destruct o.
        rewrite /=!big_ord_recl/=.

        have H: \sum_(i < m)
        \sum_(j < n) (if (i, j) \in h then c (i, j) else 0) *: delta_mx i j =
     \sum_(i < m)
        \sum_(j < n) (if (i, j) \in a :: h then c (i, j) else 0) *: delta_mx i j.
      Qed.
*)
      Lemma fn_li : lmodBasis.li fn_bset.
      Proof. rewrite/fn_bset/lmodFinSet.to_set/==>c H.
        destruct c as [c V].
        destruct H as [h [U [H S]]].
        simpl in H, S, c, h; rewrite fsFun.eqFSFun/=; clear V.
        rewrite /fn in S.
        rewrite (seq_basis _ U) in S.
        move:(matrix_sum_delta (\matrix_(i < m, j < n)(if (i, j) \in h then c (i, j) else 0))).
        under eq_bigr do under eq_bigr do rewrite mxE.
        move=>A. move/eqP in S; move:S.
        rewrite -A -matrixP/eqrel=>/=S.
        apply functional_extensionality=>b.
        move:(S b.1 b.2)=>/=.
        rewrite !mxE.
        case(c b == 0) as []eqn:E.
        by move/eqP in E.
        move/negbT in E.
        by destruct b=>/=;
        rewrite (H _ E)/=.
      Qed.
(*
      Definition elemFun_raw : fn_bset -> 'M_(m,n) -> R
      := fun ij => fun A : 'M_(m,n) => A ij.1 ij.2.
      Lemma elemFun_sca (b : fn_bset) : scalar (elemFun_raw b).
      Proof. rewrite/elemFun_raw=>r x y.
        by rewrite mxE mxE. Qed.

      Definition elemFun : fn_bset -> {scalar 'M[R]_(m,n)}
       := fun b => Linear (elemFun_sca b).
      *)
    Lemma fn_spanning : lmodBasis.span fn_bset.
    Proof. move=>A.
      move:(matrix_sum_delta A)=>W.
      rewrite pair_big/= in W.

      have HS : hasSupport (fun i => A i.1 i.2) (index_enum (prod_finType (ordinal_finType m) (ordinal_finType n))) by
      move=>b X; apply (mem_index_enum b).

      have E : hasFinSuppE (fun i => A i.1 i.2) by
      apply (ex_intro _ _ (ex_intro _ (index_enum_uniq _) HS)).

      refine(exist _ (fsFun.Pack E) _).
      refine (ex_intro _ _ (ex_intro _ (index_enum_uniq _) (ex_intro _ HS _))).
      by rewrite {2}W/=/fn eq_refl.
    Qed.

    Definition basis : lmodFinBasisType (matrix_lmodType R m n) := lmodFinBasis.Build fn_li fn_spanning.
  End Def.
  Module Exports.
    Canonical Structure fdFreeLmod_matrix (R : ringType) (m n : nat) := Eval hnf in fdFreeLmodPack (basis R m n).
  End Exports.
End freeLmodMatrix.
Export freeLmodMatrix.Exports.


Definition vector_lmodType R n := matrix_lmodType R 1 n.
Module freeLmodVector.
  Section Def.
    Variable (R : ringType) (n : nat).
    Notation ord0 := (Ordinal (ltn0Sn 0)).

    Definition fn pp := @delta_mx R 1 n ord0 pp.
    Lemma fn_injective : injective fn.
      Proof. move: (@freeLmodMatrix.fn_injective R 1 n).
        rewrite /injective/freeLmodMatrix.fn/fn=>H x y P.
        move: (H (ord0, x) (ord0, y) P).
        by rewrite !(rwP eqP).
      Qed.

      Lemma fn_nondegen : non_degenerate fn.
      Proof. move: (@freeLmodMatrix.fn_nondegen R 1 n).
        rewrite /non_degenerate/freeLmodMatrix.fn/fn=>H i.
        by move: (H (ord0, i)).
      Qed.

      Definition fn_bset := lmodFinSet.Build fn_injective fn_nondegen.

      Section Bijection.
        Lemma n_sizen : n = size (enum 'I_n).
        Proof. by rewrite -cardT !card_ord. Qed.
        (*ord_to_finBasis n_sizen (finBasis_to_ord n_size1n x).*)

        Lemma n_size1n : n = size (enum (prod_finType (ordinal_finType 1) (ordinal_finType n))).
        Proof. by rewrite -cardT card_prod !card_ord mul1n. Qed.
        Definition vect_to_mat : fn_bset -> (@freeLmodMatrix.fn_bset R 1 n) := fun x =>
        (ord0, x).
        Definition mat_to_vect : (@freeLmodMatrix.fn_bset R 1 n) -> fn_bset :=
          fun x => x.2.
        
        Lemma vect_to_matK : cancel mat_to_vect vect_to_mat.
        Proof. rewrite /vect_to_mat/mat_to_vect=>x.
          destruct x as [x1 x2]=>/=.
          destruct x1.
          by induction m; [rewrite -(proof_irrelevance _ _ (ltn0Sn 0)) |inversion i].
        Qed.

        Lemma mat_to_vectK : cancel vect_to_mat mat_to_vect.
        Proof. by rewrite /vect_to_mat/mat_to_vect=>x. Qed.
      End Bijection.

      Lemma vector_to_matrix : forall i, fn (mat_to_vect i) = freeLmodMatrix.fn_bset R 1 n i.
      Proof. rewrite/fn=>i; rewrite/freeLmodMatrix.fn_bset/freeLmodMatrix.fn.
        destruct i, s as [s S], s=>//=.
      Qed.

      Lemma fn_li : lmodBasis.li fn_bset.
      Proof. move: (@freeLmodMatrix.fn_li R 1 n)=>W C S.
        rewrite /lmodBasis.li in W.
        destruct C as [coef [Sc Hc]].
        destruct S as [s [U [H S]]].
        move: s U H S.
        rewrite/==>s U H S.
        rewrite fsFun.eqFSFun/=; clear Sc Hc.
        pose(s' := map (fun i => (Ordinal (ltn0Sn 0),i)) s).

        have U' : uniq s'.
        rewrite map_inj_in_uniq=>//.
        move=>x y X Y E.
        by inversion E.

        have H' : hasSupport (coef \o snd) s'.
        move=>b X.
        destruct b as [b' b]; simpl in X.
        rewrite /s'.

        have BB: b' == ord0 by
        destruct b'; rewrite /eq_op/=; destruct m=>//.
        move/eqP in BB; destruct BB.

        apply (map_f (fun b=> (b', b))).
        apply (H _ X).

        have Q: fsFun.finSuppE (B:= prod_eqType (ordinal_eqType 1) _) (coef \o snd) by
        apply(ex_intro _ s' (ex_intro _ U' H')).

        move:(W (fsFun.Pack Q))=>T.
        have Y: lmodLCSumsTo (B:=freeLmodMatrix.fn_bset R 1 n) {| fsFun.sort := coef \o snd; fsFun.hasFiniteSupport := Q |} 0.

        rewrite /lmodLC.li.
        refine(ex_intro _ s' (ex_intro _ U' (ex_intro _ H' _))).
        rewrite/=/s' big_map/=/freeLmodMatrix.fn/=.
        by rewrite /fn in S.
        move:(T Y).
        rewrite fsFun.eqFSFun/=/comp/==>O.
        apply functional_extensionality=>b.
        by move: (equal_f O (ord0,b)).
      Qed.

    Lemma fn_spanning : lmodBasis.span fn_bset.
    Proof. move=>/=A.
      move: (@freeLmodMatrix.fn_spanning R 1 n A)=>C;destruct C as [C S].
      have E: fsFun.finSuppE (C \o vect_to_mat). clear S.
      destruct C as [coef [c [U H]]]; simpl.
      refine(ex_intro _ (map mat_to_vect c) _).
      rewrite -(map_inj_in_uniq (f:=mat_to_vect)) in U.
      refine(ex_intro _ U _).
      move=>b X.
      rewrite/comp/vect_to_mat in X.
      rewrite -(rwP mapP).
      refine(ex_intro2 _ _ (ord0,b) (H _ X) _)=>//.
      move=>[x1 x2] [y1 y2] X Y Z.
      rewrite/mat_to_vect/= in Z.
      destruct x1, y1.
      destruct m,m0=>//.
      by rewrite Z (proof_irrelevance _ i i0).

      refine(exist _ (fsFun.Pack E) _).
      destruct S as [s [U [H S]]].
      refine(ex_intro _ (map mat_to_vect s) _).
      rewrite -(map_inj_in_uniq (f:=mat_to_vect)) in U.
      refine(ex_intro _ U _).
      have HS:hasSupport (C \o vect_to_mat) [seq mat_to_vect i | i <- s].
      move=> b X.
      rewrite/comp/vect_to_mat in X.
      rewrite -(rwP mapP).
      refine(ex_intro2 _ _ (ord0,b) (H _ X) _)=>//.
      refine(ex_intro _ HS _).
      rewrite big_map/=.
      under eq_bigr do rewrite vect_to_matK.
      rewrite /freeLmodMatrix.fn_bset/=/freeLmodMatrix.fn in S.
      move/eqP in S.
      rewrite/fn/mat_to_vect -S -(rwP eqP).
      apply eq_bigr=>i _.
      destruct i as [[i1 I1] i2]=>/=.
      destruct ord0 as [o1 O1].
      destruct i1, o1=>//.
      move=>[x1 x2] [y1 y2] _ _ Z.
      rewrite/mat_to_vect/= in Z.
      destruct x1, y1.
      destruct m,m0=>//.
      by rewrite Z (proof_irrelevance _ i i0).
    Qed.

    Definition basis : lmodFinBasisType (vector_lmodType R n) := lmodFinBasis.Build fn_li fn_spanning.
  End Def.

  Module Exports.
    Canonical fdFreeLmod_vector (R : ringType) (n : nat) := Eval hnf in fdFreeLmodPack (basis R n).
  End Exports.
End freeLmodVector.
Export freeLmodVector.Exports.

Module freeLinear.
  Section Def.
  Variable (R : ringType).

  Section Arbitrary.
    Variable (M1 M2 : freeLmodType R)
    (matrix : (freeLmod.basis M1) -> (freeLmod.basis M2) -> R).

    Record subset(M : freeLmodType R)
    := Subset { F : finType; f :> F -> freeLmod.basis M; _ : injective f;}.

    Definition linear_extension_axiom (f : {linear M1 -> M2}) :=
    forall (S1 : subset M1) (S2 : subset M2) b1 b2,
      matrix (S1 b1) (S2 b2)
      = lmodBasis.coef (S2 b2) (f ((freeLmod.basis M1) (S1 b1))).
  End Arbitrary.

  Section VectorConversion.
   Variable (M : fdFreeLmodType R) (n : nat) (E : n = size (enum (to_FinType (fdBasis M)))).

    Definition to_row_raw : M -> vector_lmodType R n  := fun x =>
    \row_(i < n)
      \fdFreeBasisCoef_(lmodFinSet.from_ord E i) x.

    Definition from_row_raw : vector_lmodType R n -> M  := fun x =>
      \sum_(b : fdBasis M)
        x (Ordinal (ltn0Sn 0)) (lmodFinSet.to_ord E b) *: (fdBasis M b).

    Lemma from_row_lin : linear to_row_raw /\ linear from_row_raw.
    Proof. split; rewrite/from_row_raw/to_row_raw=>r x y.
    rewrite -matrixP /eqrel=>i j.
    by rewrite !mxE linearP.
    rewrite scaler_sumr -big_split.
    apply eq_bigr=>i _.
    by rewrite mxE mxE scalerDl scalerA. Qed.

    Lemma from_rowK : cancel to_row_raw from_row_raw /\ cancel from_row_raw to_row_raw.
    Proof. split=>x; rewrite/from_row_raw/to_row_raw.
      move:(lmodBasis.hasSpanEq (fdBasis M) x)=>H.
      destruct H as [s [U [H S]]]; move/eqP in S.
      rewrite (lmodLC.finSuppsSumToEq H (@lmodFinBasis.hasSupport_enum _ _ (fdBasis M) x) U (enum_uniq _)) in S.
      rewrite -big_enum-S.
      apply eq_bigr=>i _.
      rewrite mxE.
      rewrite linear_sum ord_to_finBasisK scaler_suml.
      by rewrite (lmodBasis.sum_trivialises (B:=fdBasis M) (enum_uniq _) i (lmodFinBasis.hasSupport_enum (x:=x))).

      rewrite -matrixP=>i j.
      rewrite mxE linear_sum.
      under eq_bigr do rewrite linearZ (lmodBasis.orthonormP (B:=fdBasis M) (ord_to_finBasis E j)) eq_sym.
      have Q: forall k (_ : true),
        (x (Ordinal (ltn0Sn 0)) (finBasis_to_ord E k) * (if k == ord_to_finBasis E j then 1 else 0))
          = if k == ord_to_finBasis E j then
              x (Ordinal (ltn0Sn 0)) (finBasis_to_ord E k)
            else
              0
      by move=>k _; case(k == ord_to_finBasis E j); [rewrite mulr1|rewrite mulr0].
      rewrite (eq_bigr _ Q) -big_mkcond big_pred1_eq finBasis_to_ordK.
      destruct i as [i I]; destruct i=>//.
      by rewrite (proof_irrelevance _ (ltn0Sn 0) I).
    Qed.
    Definition to_row := linIsomBuildPack from_row_lin from_rowK.
  End VectorConversion.

  Section MatrixConversion.
    Variable (M N : fdFreeLmodType R)
    (m : nat) (Em : m = size (enum (to_FinType (fdBasis M))))
    (n : nat) (En : n = size (enum (to_FinType (fdBasis N)))).

    Definition to_map (f : {linear M -> N}) : {linear (vector_lmodType R m) -> (vector_lmodType R n)}
     := (to_row En) \oLin f \oLin inv(to_row Em).

    Definition from_map (f : {linear (vector_lmodType R m) -> (vector_lmodType R n)}) : {linear M -> N}
      := inv(to_row En) \oLin f \oLin (to_row Em).

    Lemma from_mapK : cancel to_map from_map.
    Proof. rewrite/from_map/to_map=>/=f.
      rewrite !linear_eq.
      apply functional_extensionality=>x.
      by rewrite -!linCompChain !(isomlK _).
    Qed.
    
    Lemma to_mapK : cancel from_map to_map.
    Proof. rewrite/from_map/to_map=>f.
      rewrite !linear_eq.
      apply functional_extensionality=>x.
      by rewrite -!linCompChain !(isomKl _).
    Qed.
  End MatrixConversion.
  End Def.
End freeLinear.





(*

  Direct Sums of Free Modules
  
    *)

Module dsFdFreeLmod.
  Module Pair.
    Section Def.
      Variable (R : ringType).
      Variable (M1 M2 : lmodType R) (B1 : lmodFinBasisType M1) (B2 : lmodFinBasisType M2).

      Section FiniteSuppSums.
        Import FiniteSupport.
        Lemma LCsumsTo_sums (C1 : lmodLCType B1) (C2 : lmodLCType B2) m1 m2 : lmodLC.sumsTo C1 m1 -> lmodLC.sumsTo C2 m2
        -> lmodLC.sumsTo (lmodLC.sum C1 C2) (m1,m2).
        Proof. move=>H1 H2.
          destruct H1 as [s1 [U1 [H1 S1]]].
          destruct H2 as [s2 [U2 [H2 S2]]].
          refine(ex_intro _ (fsFun.sum_seq s1 s2) _).
          refine(ex_intro _ (fsFun.sum_uniq U1 U2) _).
          refine(ex_intro _ (fsFun.hasFunSupp_sum H1 H2) _).
          rewrite big_cat/= !big_map/lmodSet.elem_sum.
          under (eq_bigr (r:=s1)) do rewrite /(scale _)/=/scale_pair/= scaler0.
          under (eq_bigr (r:=s2)) do rewrite /(scale _)/=/scale_pair/= scaler0.
          by rewrite dsLmod.pair_eq_seq S1 S2.
        Qed.


        Lemma LCsumsTo_sumsI (C : lmodLCType (lmodSet.sum B1 B2)) m1 m2 : lmodLC.sumsTo C (m1,m2)
            -> (lmodLC.sumsTo (fsFun.foldFSl C) m1 /\ lmodLC.sumsTo (fsFun.foldFSr C) m2).
        Proof. move=>H; split;destruct H as [h [U [E H]]].
          refine(ex_intro _ (fsFun.foldL h) _).
          refine(ex_intro _ (fsFun.foldL_uniq U) _).
          refine(ex_intro _ (fsFun.foldL_fs E) _).
          clear E U. move: m1 m2 H.
          induction h=>//m1 m2.
          rewrite !big_nil {1}/eq_op/= -(rwP andP)=>H;
          apply (proj1 H).
          destruct a; [rewrite fsFun.foldL_consl|rewrite fsFun.foldL_consr];
            rewrite !big_cons;
            rewrite /(scale _)/=/scale_pair/= scaler0 addrC eq_sym -subr_eq /(add _)/=/add_pair/= subr0 eq_sym=>H;
            move: (IHh _ _ H) => G//.
            by rewrite eq_sym subr_eq eq_sym addrC in G.

          refine(ex_intro _ (fsFun.foldR h) _).
          refine(ex_intro _ (fsFun.foldR_uniq U) _).
          refine(ex_intro _ (fsFun.foldR_fs E) _).
          clear E U; move: m1 m2 H.
          induction h=>//m1 m2.
          rewrite !big_nil {1}/eq_op/= -(rwP andP)=>H;
          apply (proj2 H).
          destruct a; [rewrite fsFun.foldR_consl|rewrite fsFun.foldR_consr];
            rewrite !big_cons;
            rewrite /(scale _)/=/scale_pair/= scaler0 addrC eq_sym -subr_eq /(add _)/=/add_pair/= subr0 eq_sym=>H;
            move: (IHh _ _ H) => G//.
            by rewrite eq_sym subr_eq eq_sym addrC in G.
        Qed.
      End FiniteSuppSums.

      Lemma pair_li : lmodBasis.li (lmodSet.sum B1 B2).
      Proof. move=>c H.
        apply (LCsumsTo_sumsI) in H. destruct H as [H1 H2].
        move: (lmodBasis.hasLI (B:=B1) H1).
        move: (lmodBasis.hasLI (B:=B2) H2).
        rewrite !lmodLC.eqFSFun/==>Z2 Z1.
        apply functional_extensionality=>b.
        destruct b;[apply (equal_f Z1 s)|apply (equal_f Z2 s)].
      Qed.
      Lemma pair_sp : lmodBasis.span (lmodSet.sum B1 B2).
      Proof. move=> m.
        move: (lmodBasis.hasSpanEq B1 m.1)=>E1.
        move: (lmodBasis.hasSpanEq B2 m.2)=>E2.
        move:(LCsumsTo_sums E1 E2)=>E.
        apply(exist _ (lmodLC.sum (lmodBasis.hasSpanLC B1 m.1) (lmodBasis.hasSpanLC B2 m.2)) E).
      Qed.

      Definition basis : lmodFinBasisType (pair_lmodType M1 M2) := lmodFinBasis.Build pair_li pair_sp.
    End Def.

    Definition fdFreeLmod (R : ringType) (m1 m2 : fdFreeLmodType R) := fdFreeLmodPack (basis (fdBasis m1) (fdBasis m2)).
    Section Results.
      Variable (R : ringType).
      Variable (M1 M2 : fdFreeLmodType R).
      Definition inj1 : {linear M1 -> fdFreeLmod M1 M2} := dsLmod.Pair.inj1 M1 M2.
      Definition inj2 : {linear M2 -> fdFreeLmod M1 M2} := dsLmod.Pair.inj2 M1 M2.

      Definition proj1 : {linear fdFreeLmod M1 M2 -> M1} := dsLmod.Pair.proj1 M1 M2.
      Definition proj2 : {linear fdFreeLmod M1 M2 -> M2} := dsLmod.Pair.proj2 M1 M2.
    End Results.

    Module Exports.
      Canonical fdFreeLmod.
    End Exports.
  End Pair.
  Export Pair.Exports.

  Module Seq.
    Section Def.
      Variable (R : ringType) (T : eqType) (I : T -> (fdFreeLmodType R)).
      Fixpoint basis (L : seq T) := match L with
      |nil    => fdBasis (null_fdFreeLmod R) : lmodFinBasisType (dsLmod.Seq.DS I nil)
      |a::L'  => (Pair.basis (fdBasis (I a)) (basis L')) : lmodFinBasisType (dsLmod.Seq.DS I (a::L'))
      end.
    End Def.

    Definition fdFreeLmod (R : ringType) (T : eqType) (I : T -> (fdFreeLmodType R)) (L : seq T) := fdFreeLmodPack (basis I L).
    
    Module Exports.
      Canonical fdFreeLmod.
    End Exports.
  End Seq.

  Section Def.
    Variable (R : ringType) (F : finType) (I : F -> (fdFreeLmodType R)).
    Definition type := Seq.fdFreeLmod I (enum F).
  End Def.
  Export Seq.Exports.
End dsFdFreeLmod.

Reserved Notation "\fbigoplus_ i F"
  (at level 36, F at level 36, i at level 0,
    right associativity,
          format "'[' \fbigoplus_ i '/ ' F ']'").

Reserved Notation "\fbigoplus F"
  (at level 36, F at level 36,
    right associativity,
          format "'[' \fbigoplus F ']'").

Reserved Notation "\fbigoplus_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
          format "'[' \fbigoplus_ ( i <- r ) '/ ' F ']'").

Reserved Notation "\fbigoplus_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50,
          format "'[' \fbigoplus_ ( i : t ) '/ ' F ']'").

Reserved Notation "\fbigoplus_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
          format "'[' \fbigoplus_ ( i 'in' A ) '/ ' F ']'").


Infix "\lmod^"  := (vector_lmodType) (at level 30) : lmod_scope.
Infix "\foplus" := (dsFdFreeLmod.Pair.fdFreeLmod) (at level 36) : lmod_scope.
Notation "\fbigoplus_ i F" := (dsFdFreeLmod.type (fun i => F)) : lmod_scope.
Notation "\fbigoplus F" := (dsFdFreeLmod.type F) : lmod_scope.
Notation "\fbigoplus_ ( i : t ) F" := (dsFdFreeLmod.type (fun i : t => F)) : lmod_scope.
Notation "\fbigoplus_ ( i 'in' A ) F" := (dsFdFreeLmod.Seq.fdFreeLmod (filter F (fun i => i \in A))) : lmod_scope.


Export dsFdFreeLmod.Pair.Exports.
Export dsFdFreeLmod.Seq.Exports.
(*
Theorem FreeModule_UniversalProperty (R : ringType) (M : fdFreeLmodType R)
    : forall (N : lmodType R) (f : (fdBasis M) -> N), 
      exists (g : {linear M -> N}),
        f = g \o (fdBasis M).
  Proof.
  Admitted.
  *)

Close Scope ring_scope.
Close Scope lmod_scope.