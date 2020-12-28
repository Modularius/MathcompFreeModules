(******************************************************************************)
(**)
(******************************************************************************)
(* Let R : ringType and M : lmodType R                                        *)
(******************************************************************************)
(* lmodSetType M == a record consisting of a type 'sort' a function           *)
(*                'elem' : sort -> M, and proofs of (injective elem)          *)
(*                and (non_degenerate elem).                                  *)
(*                injective elem == forall x y : T, elem x = elem y -> x = y  *)
(*                non_degenerate elem == forall x : T, elem x != 0            *)
(*                S : lmodSetType M coerces to its type T and function elem   *)
(*                so b : S is shorthand for b : (sort S)                      *)
(*                and S b for (elem S) b.                                     *)
(******************************************************************************)
(* Let S : lmodSetType M                                                      *)
(******************************************************************************)
(* typeIsNonDegenerate S == the proof that S is non_degenerate                *)
(* typeIsInjective S == the proof that S  is injective                        *)
(******************************************************************************)
(* lmodOrthoType S == a record consisting of a function                       *)
(*                    'proj' : S -> {scalar M} and a proof of                 *)
(*                    (orthonormP proj)                                       *)
(*                    orthonormP proj == forall b1 b2 : S, proj b1 (S b2)     *)
(*                                         = if b1 == b2 then 1 else 0        *)
(*                    O : lmodOrthoType S coerces to S                        *)
(*                    so b : O and O b work as for lmodSetType                *)
(******************************************************************************)
(* Let O : lmodOrthoType S                                                    *)
(******************************************************************************)
(* orthonormP O     == orthonormP (lmodBasisProj O)                          *)
(* lmodBasisProj O  == the 'proj : O -> {scalar M} function                   *)
(* \basisProj_b^(O) == lmodBasisProj O b : {scalar M}                         *)
(* typeIsNonDegenerate O == the proof that O is non_degenerate                *)
(* typeIsInjective O == the proof that O is injective                         *)
(******************************************************************************)
(* lmodBasisType O == a record consisting of a proof of                       *)
(*                    basisP (lmodBasisProj O)                                *)
(*                    basisP proj == forall m1 m2 : M,                        *)
(*                      reflect (forall b : O, proj b m1 = proj b m2)         *)
(*                              (m1 == m2)                                    *)
(*                    B : lmodBasisType O coerces to O                        *)
(*                    so b : B and B b work as for lmodSetType                *)
(******************************************************************************)
(* Let B : lmodBasisType O                                                    *)
(******************************************************************************)
(* basisP B              == basisP (lmodBasisProj O)                          *)
(* lmodBasisProj B       == the 'proj : B -> {scalar M} function              *)
(* \basisProj_b^(B)      == lmodBasisProj B b : {scalar M}                    *)
(* typeIsNonDegenerate B == the proof that B is non_degenerate                *)
(* typeIsInjective B     == the proof that B is injective                     *)
(******************************************************************************)
(* lmodFinSetType M == a record consisting of a finType 'sort' and the        *)
(*                     mixin of an lmodSetType for type sort.                 *)
(*                     F : lmodBasisType M coerces to an lmodSetType          *)
(*                     so f : F and F f work as for lmodSetType               *)
(*                     However lmodFinSetType does not coerce to a finType    *)
(*                     There is an explicit function for this *)
(******************************************************************************)
(* Let F : lmodFinSetType M                                                   *)
(******************************************************************************)
(* typeIsNonDegenerate F == the proof that F is non_degenerate                *)
(* typeIsInjective F == the proof that F  is injective                        *)
(* to_FinType F == the underlying finType of F                                *)
(******************************************************************************)
(* Note that all F : lmodFinSetType M are bijective to some ordinal type,     *)
(* to establish the bijection we require:                                     *)
(*  1) n : nat                                                                *)
(*  2) and a proof K : n = size (enum (to_FinType F))                         *)
(*  finBasis_to_ord K f == ordinal of 'I_n corresponding to f : F             *)
(*  ord_to_finBasis K i == element of F corresponding to i : 'I_n             *)
(******************************************************************************)
(* lmodFinBasisType O == a record consisting of a proof of                    *)
(*                    basisP (lmodBasisProj O)                                *)
(*                    basisP proj == forall m1 m2 : M,                        *)
(*                      reflect (forall b : O, proj b m1 = proj b m2)         *)
(*                              (m1 == m2)                                    *)
(*                    B : lmodBasisType O coerces to O                        *)
(*                    so b : B and B b work as for lmodSetType                *)
(******************************************************************************)
(* Let B : lmodFinBasisType M                                                 *)
(******************************************************************************)
(* lmodFinBasis_to_lmodBasis B == the underlying lmodBasisType M              *)
(******************************************************************************)



Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From mathcomp Require Import ssreflect ssrfun eqtype fintype seq bigop finset.

Require Import Modules Linears FiniteSupport lmodLC.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.


Reserved Notation "\basisProj_ b ^( B )"
  (at level 36, B at level 36, b at level 0,
    right associativity,
          format "'[' \basisProj_ b '^(' B ) ']'").



Module lmodBasis.
  Section Def.
    Variable (R : ringType) (M : lmodType R).

    Definition li (B : lmodSetType M)
    := forall (C : lmodLCType B), lmodLC.li C.

    Definition isnonzero (B : lmodSetType M) (T : seq (B*R)) := ~~has (eq_op^~0) (map snd T).
    Lemma nonzero_cons (B : lmodSetType M) (T : lmodLCType B) (a : B*R) c : isnonzero (a::c) -> isnonzero c.
    Proof. by rewrite/isnonzero/= negb_or -(rwP andP)=>U; rewrite (proj2 U). Qed.

    Definition span (B : lmodSetType M)
    := forall (m : M),
        {C : lmodLCType B | (lmodLC.sumsTo C m)}.

    Record mixin (B : lmodSetType M) := Mixin {
      is_li : li B;
      spans : span B;
    }.

    Record type := Pack { sort : _; class_of : mixin sort; }.

    Definition hasLI (B : type) (C : lmodLCType (sort B)) := @is_li _ (class_of B) C.
    Definition hasSpanLC (B : type) (m : M) := sval (@spans _ (class_of B) m).

    Lemma hasSpanEq (B : type) (m : M) : lmodLC.sumsTo (hasSpanLC B m) m.
    Proof. move: (proj2_sig (@spans _ (class_of B) m))=>P.
      destruct P as [s [S Eq]].
      refine(ex_intro _ s _); refine(ex_intro _ S _)=>//.
    Qed.

    Definition Build (T : eqType) (elem : T -> M)
      (I : injective elem) (ND : non_degenerate elem)
      (LI : li (lmodSet.Build I ND))
      (Sp : span (lmodSet.Build I ND))
    : type := Pack (Mixin LI Sp).

    Local Coercion sort : type >-> lmodSetType.
    Local Coercion class_of : type >-> mixin.
  End Def.

  Module Exports.
    Notation lmodBasisType := type.
    Coercion sort : type >-> lmodSetType.
    Coercion class_of : type >-> mixin.
  End Exports.
  Export Exports.
  
  Section Results.
    Export lmodBasis.Exports GRing.
    Variable (R : ringType) (M : lmodType R) (B : type M).

    Lemma sumsToZero_null (C : lmodLCType B) : lmodLC.sumsTo C 0 -> C = nullFSType R B.
    Proof. move=>H; by apply (hasLI H). Qed.

    Definition is_add_ind_fn (xy x y : M) := (fun i : B => (sval (spans B xy)) i - (sval (spans B x) i + sval (spans B y) i)).
 
    Lemma is_additive (x y : M) : (hasSpanLC B x) <+> (hasSpanLC B y) = (hasSpanLC B (x + y)).
    Proof.
      move:(hasSpanEq B x) (hasSpanEq B y) (hasSpanEq B (x + y)).
      rewrite/hasSpanLC lmodLC.eqFSFun/=/lmodLCSumsTo/==>Ex Ey Exy.
      destruct Ex as [c [Uc [Fc Ex]]],  Ey as [d [Ud [Fd Ey]]], Exy as [cd [Ucd [Fcd Exy]]].

      move:(fsFun.hasSupport_catl d Fc)=>Fc'; move/fsFun.hasSupport_undup
        /(fsFun.hasSupport_catl cd)/fsFun.hasSupport_undup in Fc'.
      move:(fsFun.hasSupport_catr c Fd)=>Fd'; move /fsFun.hasSupport_undup
        /(fsFun.hasSupport_catl cd)/fsFun.hasSupport_undup in Fd'.

      move:(fsFun.hasSupport_undup (fsFun.hasSupport_catr (undup (c ++ d)) Fcd))=>Fcd'.
      rewrite (lmodLC.finSuppsSumToEq Fc Fc' Uc (undup_uniq _)) in Ex; move/eqP in Ex.
      rewrite (lmodLC.finSuppsSumToEq Fd Fd' Ud (undup_uniq _)) in Ey; move/eqP in Ey.
      rewrite (lmodLC.finSuppsSumToEq Fcd Fcd' Ucd (undup_uniq _)) in Exy.
      move: Exy; rewrite -{3}Ex-{3}Ey -big_split/= -subr_eq0 -sumrB.
      under eq_bigr do rewrite -scalerDl -scalerBl; move=>Exy.

      have FS: fsFun.hasSupport (is_add_ind_fn (x + y) x y)
        (undup (undup (c ++ d) ++ cd)).
      rewrite/is_add_ind_fn=>b C.
      case(~~(sval (spans B x) b == 0)) as []eqn:Ec.
      by apply (Fc' b Ec).
      case(~~(sval (spans B y) b == 0)) as []eqn:Ed.
      by apply (Fd' b Ed).
      move/negbFE/eqP in Ec.
      move/negbFE/eqP in Ed.
      rewrite Ec Ed addr0 subr0 in C.
      by apply (Fcd' b C).

      have E: fsFun.finSuppE (is_add_ind_fn (x + y) x y).
      refine(ex_intro _ (undup (undup (c ++ d) ++ cd)) _).
      apply(ex_intro _ (undup_uniq _) FS).

      have S:lmodLCSumsTo (fsFun.Pack E) 0.
      refine(ex_intro _ (undup (undup (c ++ d) ++ cd)) (ex_intro _ (undup_uniq _) _)).
      apply(ex_intro _ FS Exy).

      clear FS; move:(@hasLI _ _ B (fsFun.Pack E) S)=>/=K.
      apply lmodLC.eqFSFun in K;simpl in K.
      apply functional_extensionality=>b.
      move:(equal_f K b)=>T.
      move/eqP in T.
      rewrite subr_eq0 eq_sym in T.
      by move/eqP in T.
    Qed.

    Definition is_sca_ind_fn r (x : M) := (fun i => (sval (spans B (r *: x)) i) - r * (sval (spans B (x)) i)).
 
    Lemma is_scalar (r : R) (x : M) : r <*:> (hasSpanLC B x) = (hasSpanLC B (r *: x)).
    Proof.
      move:(hasSpanEq B x) (hasSpanEq B (r *: x)).
      rewrite/hasSpanLC lmodLC.eqFSFun/=/lmodLCSumsTo/==>Ex Erx.
      destruct Ex as [c [Uc [Fc Ex]]], Erx as [d [Ud [Fd Erx]]].

      move:(fsFun.hasSupport_undup (fsFun.hasSupport_catl d Fc))=>Fc'.
      move:(fsFun.hasSupport_undup (fsFun.hasSupport_catr c Fd))=>Fd'.
      
      rewrite (lmodLC.finSuppsSumToEq Fc Fc' Uc (undup_uniq _)) in Ex; move/eqP in Ex.
      rewrite (lmodLC.finSuppsSumToEq Fd Fd' Ud (undup_uniq _)) in Erx.
      move: Erx; rewrite -{3}Ex -subr_eq0 scaler_sumr -sumrB.
      under eq_bigr do rewrite scalerA -scalerBl; move=>Erx.

      have FS: fsFun.hasSupport (is_sca_ind_fn r x)
        (undup (c ++ d)).
      rewrite /is_sca_ind_fn/fsFun.hasSupport=>b C.
      case(~~(sval (spans B x) b == 0)) as []eqn:Ec.
      by apply (Fc' b Ec).
      move/negbFE/eqP in Ec.
      rewrite Ec mulr0 subr0 in C.
      apply (Fd' b C).

      have E: fsFun.finSuppE (is_sca_ind_fn r x).
      refine(ex_intro _ (undup (c ++ d)) _).
      apply(ex_intro _ (undup_uniq _) FS).

      have S:lmodLCSumsTo (fsFun.Pack E) 0.
      refine(ex_intro _ (undup (c ++ d)) _);
      apply (ex_intro _ (undup_uniq _) (ex_intro _ FS Erx)).

      clear FS; move:(@hasLI _ _ B (fsFun.Pack E) S)=>/=K.
      apply lmodLC.eqFSFun in K;simpl in K.
      apply functional_extensionality=>b.
      move:(equal_f K b)=>T.
      move/eqP in T.
      rewrite subr_eq0 eq_sym in T.
      by move/eqP in T.
    Qed.
  End Results.

  Section Coef.
    Variable (R : ringType) (M : lmodType R) (B : type M).

    Definition coef_raw (b : B) (m : M) : R
      := (hasSpanLC B m) b.

    Lemma coef_sca (b : B) : scalar (coef_raw b).
    Proof. rewrite/coef_raw=>r x y.
      by rewrite -is_additive -is_scalar/=.
    Qed.

    Definition coef b := Linear (coef_sca b).
  End Coef.

  Section Results.
    Export lmodBasis.Exports GRing.
    Variable (R : ringType) (M : lmodType R) (B : type M).

    Lemma BasisElem_hasSupport (b : B) : hasSupport (hasSpanLC B (B b)) [:: b].
    Proof.
      move:(hasLI (lmodLC.sumToElem_sumToZero (hasSpanEq B (B b)))).
      rewrite fsFun.eqFSFun/==>Z.
      move=>c X.
      move:(equal_f Z c)=>Y.
      case(c == b) as []eqn:E.
      by move/eqP in E; rewrite E in_cons eq_refl orTb.
      rewrite addr0 in Y.
      by rewrite Y eq_refl in X.
    Qed.

    Lemma orthonormP (b1 b2 : B) : coef b1 (B b2) = if b1 == b2 then 1 else 0.
    Proof. rewrite/= /coef_raw.
      move:(hasLI (lmodLC.sumToElem_sumToZero (hasSpanEq B (B b2)))).
      rewrite fsFun.eqFSFun/==>S.
      case(b1 == b2) as []eqn:E.
        move/eqP in E; rewrite -E.
        move:(equal_f S b1)=>Y.
        by move/eqP in Y; rewrite -E eq_refl subr_eq0 in Y; move/eqP in Y.

        move:(equal_f S b1)=>Y.
        by rewrite E addr0 in Y.
    Qed.

    Lemma sum_trivialises (S : seq B) (U : uniq S) (b1 : B) (x : M) : (hasSupport (lmodBasis.hasSpanLC B x) S) ->
      \sum_(b2 <- S) (coef b1 (lmodBasis.hasSpanLC B x b2 *: B b2)) *: B b1
      = (coef b1 x) *: B b1.
    Proof. move=>H.
      move:(lmodBasis.hasSpanEq B x)=>Z.
      destruct Z as [s [U' [H' Z]]]; move/eqP in Z.
      by rewrite -scaler_suml -linear_sum (lmodLC.finSuppsSumToEq H H' U U')-{2}Z.
    Qed.
  End Results.

  Section Isomorphism.
    Export lmodBasis.Exports GRing.
    Variable (R : ringType) (M1 M2 : lmodType R) (f : linIsomType M1 M2)
    (B : type M1).
    Lemma inj_ : injective (f \o B).
    Proof. rewrite/comp=>x y H.
      move: (congr1 (inv(f)) H).
      rewrite !isomlK=>H2.
      apply (typeIsInjective H2).
    Qed.
    Lemma nondeg_ : non_degenerate (f \o B).
    Proof. move=>b.
      rewrite -(rwP negP) -(rwP eqP)=>H.
      move: (congr1 (inv(f)) H).
      rewrite !isomlK linear0 (rwP eqP)=>H2.
      move: (@typeIsNonDegenerate _ _ _ b).
      by rewrite H2.
    Qed.
    Definition bset := lmodSet.Build inj_ nondeg_.

    Lemma li_ : li bset.
    Proof. rewrite/bset=> C H.
      destruct C as [coef [c [U E]]].
      destruct H as [s [Us [H S]]].
      move:coef s Us E H S.
      rewrite /lmodSet.to_Type/=.
      move=>coef s Us E H S.
      rewrite fsFun.eqFSFun/=; clear c U E.

      move/eqP/(congr1 (isom_linmapI f)) in S; move:S.
      rewrite /comp linear_sum linear0.
      under eq_bigr do rewrite linearZ_LR/=(linIsom.isomfK f).
      rewrite(rwP eqP)=>/=S.

      have J : hasFinSuppE coef by
      apply (ex_intro _ s (ex_intro _ Us H)).

      have K : lmodLCSumsTo (fsFun.Pack J) 0 by
      apply (ex_intro _ s (ex_intro _ Us (ex_intro _ H S))).

      move:(hasLI K); by rewrite fsFun.eqFSFun.
    Qed.

    Lemma span_ : lmodBasis.span bset.
    Proof. move=>m; move: (hasSpanEq B (inv(f) m))=>X.
      destruct (hasSpanLC B (inv(f) m)) as [coef E].
      have FS: fsFun.finSuppE (B:=bset) coef by
      destruct E as [e [U F]];
      apply(ex_intro _ e (ex_intro _ U F)).
      refine (exist _ (fsFun.Pack FS) _).
      destruct X as [c [U [D S]]].
      refine (ex_intro _ c (ex_intro _ U (ex_intro _ D _))).
      move/eqP/(congr1 f)/eqP in S; move:S.
      rewrite isomKl linear_sum.
      by under eq_bigr do rewrite linearZ.
    Qed.

    Definition isomorphicBasis : type M2
      := Build li_ span_.
  End Isomorphism.
End lmodBasis.
Export lmodBasis.Exports.

Notation "\basisProj_ b ^( B )" := (@lmodBasis.coef _ _ B b) : lmod_scope.





Module lmodFinSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R).
    Record class (T : finType) := Class {
      base : lmodSet.mixin M T;
    }.

    Record type := Pack { sort : _; class_of : class sort; }.

    Definition Build {T : finType} (elem : T -> M) (I : injective elem) (ND : non_degenerate elem)
    := Pack (Class (lmodSet.Build I ND)).

    Section Seq.
      Variable (s : seq M) (H : all (fun m => m != 0) s).
      Definition elem_seq (t : seq_sub s) : M := ssval t.
      Lemma inj_seq : injective elem_seq.
        rewrite /elem_seq/==>x y W.
        by rewrite (rwP eqP)/eq_op/= W.
      Qed.
      Lemma nondeg_seq : non_degenerate elem_seq.
      Proof. rewrite/elem_seq/==>x.
        move:H=>H2; move/allP in H2.
        by move:(H2 (ssval x) (ssvalP x)).
      Qed.
      Definition seq := Build inj_seq nondeg_seq.
    End Seq.

    Section Lemmas.
      Variable (T : type).
      Definition to_set
      := lmodSet.Pack (base (class_of T)).

      Variable (n : nat) (K : n = size (enum (sort T))).
      Definition to_ord : sort T -> 'I_n :=
      eq_rect_r (fun n : nat => sort T -> 'I_n) 
        (eq_rect #|sort T| (fun n : nat => sort T -> 'I_n)
          enum_rank (size (enum (sort T))) (cardT (sort T))) K.

      Definition from_ord : 'I_n -> sort T :=
      eq_rect_r (fun n : nat => 'I_n -> sort T) 
        (eq_rect #|sort T| (fun n : nat => 'I_n -> sort T)
          enum_val (size (enum (sort T))) (cardT (sort T))) K.

      Lemma from_ordK : cancel to_ord from_ord.
      Proof. rewrite/to_ord/from_ord/eq_rect_r/eq_rect.
        destruct (cardT (sort T)), (Logic.eq_sym K)=>x.
        by rewrite enum_rankK.
      Qed.

      Lemma to_ordK : cancel from_ord to_ord.
      Proof. rewrite/to_ord/from_ord/eq_rect_r/eq_rect.
        destruct (cardT (sort T)), (Logic.eq_sym K)=>x.
        by rewrite enum_valK.
      Qed.
    End Lemmas.
  End Def.

  Module Exports.
    Notation lmodFinSetType := type.
    Notation to_FinType := sort.
    Coercion to_set : type >-> lmodSetType.
    Notation finBasis_to_ord := to_ord.
    Notation ord_to_finBasis := from_ord.
    Notation finBasis_to_ordK := to_ordK.
    Notation ord_to_finBasisK := from_ordK.
  End Exports.
End lmodFinSet.
Export lmodFinSet.Exports.

Module lmodFinBasis.
  Section Def.
    Variable (R : ringType) (M : lmodType R).
    Record mixin (T : lmodFinSetType M) := Mixin {
      base : lmodBasis.mixin T;
    }.

    Record type := Pack { sort : _; class_of : mixin sort; }.

    Definition Build (T : finType) (elem : T -> M)
    (I : injective elem) (ND : non_degenerate elem)
    (LI : lmodBasis.li (lmodFinSet.Build I ND))
    (Sp : lmodBasis.span (lmodFinSet.Build I ND))
    : type := Pack (Mixin (lmodBasis.Mixin LI Sp)).

    Definition basis_number (B : type) := #|(to_FinType (sort B))|.

    Lemma typeSpanning (T : type) : lmodBasis.span (sort T).
    Proof. destruct T as [t B], B as [B], B; apply spans. Qed.

    Lemma typeLI (T : type) : lmodBasis.li (sort T).
    Proof. destruct T as [t B], B as [B], B; apply is_li. Qed.
  End Def.

  Section To.
    Variable (R : ringType) (M : lmodType R).
    Definition to_lmodBasis (B : type M)
    := lmodBasis.Pack (base (class_of B)).
  End To.
  Section From.
    Variable (R : ringType) (M : lmodType R) (T : lmodBasisType M) (finClass : Finite.class_of T).

    Definition bset := @lmodFinSet.Build _ M (Finite.Pack finClass) T (@typeIsInjective _ _ T) (@typeIsNonDegenerate _ _ T).
    Lemma hasFinSuppP coef s : fsFun.hasSupport (B:=T) coef s <-> fsFun.hasSupport (R:=R) (B:=bset) coef s.
    Proof. split=>H b W; move:(H b W);
        [rewrite -(mem_map (f:=fun b : T => b : bset))| rewrite -(mem_map (f:=fun b : bset => b : T))];
        by [rewrite map_id | |rewrite map_id |].
    Qed.
    Lemma finSupp_uniqP s : @uniq (lmodSet.sort T) s <-> @uniq (lmodSet.sort bset) s. 
    Proof. split=>U.
      by rewrite -(map_inj_in_uniq (f:=fun b : T => b : bset)) in U; [rewrite map_id in U|].
      by rewrite -(map_inj_in_uniq (f:=fun b : bset => b : T)) in U; [rewrite map_id in U|].
    Qed.

    Lemma finSuppP coef : fsFun.finSuppE (B:=T) coef <-> fsFun.finSuppE (R:=R) (B:=bset) coef.
    Proof. split=>H; destruct H as [s [U F]]; refine(ex_intro _ s _).
      move/finSupp_uniqP in U.
      refine(ex_intro _ U _).
      by move/hasFinSuppP in F.

      move/finSupp_uniqP in U.
      refine(ex_intro _ U _).
      by move/hasFinSuppP in F.
    Qed.

    Lemma lmodLCSumsToP (C : lmodLCType bset) (E : fsFun.finSuppE (B:=T) C) m
    : lmodLCSumsTo (B:=bset) C m <-> lmodLCSumsTo (fsFun.Pack E) m.
    rewrite/bset/=/lmodFinSet.to_set/=/lmodLCSumsTo/=.
    split=>H; destruct H as [s [U [H S]]];
    move/finSupp_uniqP in U;
    move/hasFinSuppP in H;
    apply (ex_intro _ s (ex_intro _ U (ex_intro _ H S))).
    Qed.

    Lemma li_ : lmodBasis.li bset.
    Proof.
      move=>/=C S.
      have E: fsFun.finSuppE (B := T) C.
      rewrite finSuppP.
      destruct C as [coef C].
      by apply C.
      move/(lmodLCSumsToP E) in S.
      move:(lmodBasis.hasLI S).
      by rewrite !lmodLC.eqFSFun.
    Qed.

    Lemma span_ : lmodBasis.span bset.
    Proof. move=>m.
      move: (lmodBasis.hasSpanEq T m)=>X.

      have E: fsFun.finSuppE (B := bset) (lmodBasis.hasSpanLC T m) by
      clear X;destruct (lmodBasis.hasSpanLC T m) as [coef C]=>/=;
      move/finSuppP in C.

      refine (exist _ (fsFun.Pack E) _).
      destruct X as [s [U [H S]]].
      move/finSupp_uniqP in U;
      move/hasFinSuppP in H;
      apply(ex_intro _ s (ex_intro _ U (ex_intro _ H S))).
    Qed.
    
    Definition from_lmodBasis : type M
    := Build li_ span_.
  End From.

  Module Exports.
    Notation basis_number := basis_number.
    Notation lmodFinBasisType := type.
    Coercion class_of : type >-> mixin.
    Coercion sort : type >-> lmodFinSetType.
    Coercion to_lmodBasis : type >-> lmodBasisType.
    Notation lmodBasis_to_finLmodBasis := from_lmodBasis.
    Notation lmodFinBasis_to_lmodBasis := to_lmodBasis.
  End Exports.

  Section Results.
    Export Exports GRing.
    Variable (R : ringType) (M : lmodType R) (B : type M) (x : M).
    Lemma hasSupport_enum: hasSupport (lmodBasis.hasSpanLC B x) (enum B).
    Proof. move=>b B'; by rewrite mem_enum. Qed.

    End Results.
End lmodFinBasis.
Export lmodFinBasis.Exports.

Close Scope ring_scope.
