(******************************************************************************)
(* Dr Daniel Kirk (c) 2021                                                    *)
(******************************************************************************)
(* Let R : ringType and M : lmodType R                                        *)
(******************************************************************************)
(* lmodSetType M == a record consisting of an eqType 'sort' a function        *)
(*                  'elem' : sort -> M, and proofs of (injective elem)        *)
(*                  and (non_degenerate elem).                                *)
(*                  injective elem == forall x y, elem x = elem y -> x = y    *)
(*                  non_degenerate elem == forall x : T, elem x != 0          *)
(*                  B : lmodSetType M coerces to its type T and function elem *)
(*                  so b : B is shorthand for b : (sort B)                    *)
(*                  and S b for (elem B) b.                                   *)
(******************************************************************************)
(* Let B : lmodSetType M                                                      *)
(******************************************************************************)
(* typeIsInjective B == a proof that (sort B) is injective                    *)
(* typeIsNonDegenerate B == a proof that (sort B) is non-degenerate           *)
(******************************************************************************)
(* Let f : B -> R and s : seq B                                               *)
(******************************************************************************)
(*  lmodLCsumsTo C m  == a proof that there exists a sequence (s : seq B)  *)
(*                          without duplicates such that (hasSupport C s) and *)
(*                               \sum_(b <- s)(C b) *: (B b) == m.            *)
(*  eqLCSumsTo s1 s2  == given proofs of (hasSupport C s1) and             *)
(*                          (hasSupport C s2) this is a proof of              *)
(*                          \sum_(b <- s1)(C b) *: (B b)                      *)
(*                            = \sum_(b <- s2)(C b) *: (B b)                  *)
(******************************************************************************)
(*   lmodLCType B   == a record consisting of a function sort : B -> R        *)
(*                     and a proof of finSuppE sort                           *)
(*                     C : lmodLCType B coerces to sort                       *)
(******************************************************************************)
(* lmodLCNullType B ==                                                        *)
(* lmodLCUnitType B ==                                                        *)
(******************************************************************************)
(* Let r : R and C D : lmodLCType B                                           *)
(******************************************************************************)
(* lmodLCAdd C D    ==                                                        *)
(* lmodLCScale r C  ==                                                        *)
(******************************************************************************)


Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From mathcomp Require Import ssreflect ssrfun eqtype fintype seq bigop choice.

Require Import Modules Linears FiniteSupport.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Open Scope ring_scope.
Open Scope lmod_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Module lmodSet.
  Section Def.
    Variable (R : ringType) (M : lmodType R).
    Definition non_degenerate {T : Type} (elem : T -> M) := forall b : T, elem b != 0%R.

    Record mixin (T : eqType) := Mixin {
      elem : T -> M;
      _ : injective elem;
      _ : non_degenerate elem;
    }.

    Record type := Pack { sort : _; class_of : mixin sort; }.

    Definition Build {T : eqType} (elem : T -> M) (I : injective elem) (ND : non_degenerate elem)
     := Pack (Mixin I ND).

    Lemma typeIsInjective (T : type) : injective (elem (class_of T)).
    Proof. by destruct (class_of T)=>/=. Qed.

    Lemma typeIsNonDegenerate (T : type) : non_degenerate (elem (class_of T)).
    Proof. by destruct (class_of T)=>/=. Qed.

    Definition to_Type (T : type) : Type := (sort T).
  End Def.

  Module Exports.
    Notation lmodSetType := type.
    Notation non_degenerate := non_degenerate.
    Notation typeIsInjective := typeIsInjective.
    Notation typeIsNonDegenerate := typeIsNonDegenerate.
    Coercion to_Type : type >-> Sortclass.
    Coercion elem : mixin >-> Funclass.
    Coercion class_of : type >-> mixin.
    Coercion sort : type >-> eqType.
  End Exports.
  Export Exports.

  Section Sum.
    Variable (R : ringType) (M1 M2 : lmodType R) (B1 : type M1) (B2 : type M2).
      Definition elem_sum (t : B1 + B2) : M1*M2 := match t with
        |inl t' => (B1 t',0)
        |inr t' => (0,B2 t') end.
      Lemma inj_sum : injective elem_sum.
      Proof. rewrite /elem_sum=>/=x y H.
        destruct x as [s|s], y; inversion H.
        by rewrite(typeIsInjective H1).
        move:(typeIsNonDegenerate s); by rewrite H1 eq_refl.
        move:(typeIsNonDegenerate s); by rewrite H2 eq_refl.
        by rewrite(typeIsInjective H1).
      Qed.
      Lemma nondeg_sum : non_degenerate elem_sum.
      Proof.  rewrite /comp/elem_sum=>x. rewrite /eq_op/=.
        destruct x as [s|s]; rewrite/= eq_refl; [rewrite andbT|rewrite andTb];
        apply (typeIsNonDegenerate s).
      Qed.
    Definition sum := Build inj_sum nondeg_sum.
  End Sum.
End lmodSet.
Export lmodSet.Exports.







Import GRing.

Module lmodLC.
  Section Def.
    Variable (R : ringType) (M : lmodType R) (B : lmodSetType M).

    Definition type := (FSType R B).

    Lemma eqFSFun (C D : type) : C = D <-> (fsFun.sort C) = (fsFun.sort D).
    Proof. split; destruct C, D=>/=H. by inversion H.
    by destruct H; rewrite (proof_irrelevance _ hasFiniteSupport0 hasFiniteSupport).
    Qed.

    Definition sumsTo (C : type) m
      := exists s (_ : uniq s) (_ : hasSupport C s), \sum_(b <- s)(C b) *: (B b) == m.
  End Def.
  
  Module Exports.
    Notation lmodLCType := type.
    Notation lmodLCSumsTo := sumsTo.
  End Exports.

  Section Null.
    Variable (R : ringType) (M : lmodType R) (B : lmodSetType M).

    Lemma null_sumsTo : sumsTo (nullFSType R B) 0.
    Proof. rewrite/sumsTo.
      destruct (fsFun.null_finSuppE R B) as [n [NU NH]].
      refine(ex_intro _ n (ex_intro _ NU (ex_intro _ NH _)))=>/=.
      under eq_bigr do rewrite -(GRing.mulr0 0) -GRing.scalerA.
      by rewrite -GRing.scaler_sumr  GRing.scale0r.
    Qed.
  End Null.

  Section Singleton.
    Variable (R : ringType) (M : lmodType R) (B : lmodSetType M)
      (b : B) (r : R) (NZ : r != 0).

    Lemma unit_sumsTo : sumsTo (unitFSType b r) (r*:(B b)).
    Proof. rewrite/sumsTo/unitFSType/=.
      refine(ex_intro _ [::b] (ex_intro _ is_true_true _)).
      have E: hasSupport (fun b' => if b' == b then r else 0) [:: b] by
      rewrite/hasSupport=>b' F;
      case(b' == b) as []eqn:E; [rewrite in_cons E| rewrite eq_refl in F].
      refine(ex_intro _ E _).
      by rewrite big_seq1 eq_refl.
    Qed.
  End Singleton.


  Section Results.
    Variable (R : ringType) (M : lmodType R) (B : lmodSetType M).
    Import Exports.
    Definition li (C : type B) := sumsTo C 0 -> C = nullFSType R B.


    Section SumsTo.
      Lemma zeroLCSumsTo (C : B -> R) s : (hasSupport C s) -> (hasSupport C nil)
        -> \sum_(b <- s)(C b) *: (B b) == 0.
      Proof. rewrite/hasSupport=>H1 H2.
        induction s. by rewrite big_nil.
        rewrite big_cons.
        case(~~(C a == 0)) as []eqn:E.
        move:(H2 a E); rewrite in_nil=>//.
        apply negbFE in E; move/eqP in E.
        rewrite E scale0r add0r IHs=>//.
        move=>b S; move:(H1 b S)=>H; destruct H=>//.
        move:(H2 b S); rewrite in_nil=>//.
      Qed.


      Definition funOneMinus (s : seq B) (C : B -> R) (a b : B)
       := if b == a then if a \in s then 0 else -C b else C b.

      Lemma fsOneMinusA a s1 s2 (C : B -> R) (H1 : hasSupport C s1) (H2 : hasSupport C (a::s2)) : hasSupport (funOneMinus s1 C a) s2.
      Proof.
        rewrite/funOneMinus=>b D.
        case(b == a) as []eqn:A1.
        case(a \in s1) as []eqn:A2.
        by rewrite A2 eq_refl in D.
        rewrite A2 oppr_eq0 in D.
        move/eqP in A1.
        move:(H1 b D); rewrite A1 A2=>//.
        by move:(H2 b D); rewrite in_cons-(rwP orP) A1 =>F; destruct F=>//.
      Qed.

      Lemma fsOneMinusB a s1 s2 (C : B -> R) (H1 : hasSupport C s1) (H2 : hasSupport C (a::s2)) : hasSupport (funOneMinus s1 C a) (undup(a::s1)).
      Proof.
        rewrite/funOneMinus=>b D.
        case(b == a) as []eqn:A1.
        case(a \in s1) as []eqn:A2.
        by rewrite A2 eq_refl in D.
        rewrite A2 oppr_eq0 in D.
        move/eqP in A1.
        move:(H1 b D); rewrite A1 A2=>//.
        move:(H2 b D); rewrite mem_undup in_cons-(rwP orP) A1 =>F; destruct F=>//.
        by rewrite in_cons (H1 b D) orbT.
      Qed.


      Lemma RHSeq (C : B -> R) a s1 s2
      (H1 : hasSupport C s1)
      (H2 : hasSupport C (a::s2))
      (U1 : uniq s1) (A : a \notin s2)
      (U2 : uniq s2) (E : ~~ (C a == 0))
       : \sum_(j <- s2) C j *: B j = \sum_(b <- s2) (funOneMinus s1 C a b) *: B b.
      Proof. rewrite/funOneMinus !big_seq.
        apply eq_bigr=>b P.
        case(b == a) as []eqn:E1=>//.
        move/eqP in E1; destruct E1.
        by rewrite P in A.
      Qed.

      Lemma in_cat (T : eqType) (s : seq T) x : x \in s -> exists s1 s2, s = (s1 ++ [::x] ++ s2).
      Proof.
        move:x.
        induction s=>x.
        by rewrite in_nil.
        rewrite in_cons -(rwP orP) => H.
        destruct H.
        refine(ex_intro _ nil _).
        refine(ex_intro _ s _).
        move/eqP in H.
        by rewrite cat0s H cat1s.
        destruct(IHs x H) as [s1 [s2 H2]].
        refine(ex_intro _ (a::s1) _).
        refine(ex_intro _ s2 _).
        by rewrite cat_cons H2.
      Qed.

      Lemma LHSeq (C : B -> R) a s1 s2
      (H1 : hasSupport C s1)
      (H2 : hasSupport C (a::s2))
      (U1 : uniq s1) (A : a \notin s2)
      (U2 : uniq s2) (E : ~~ (C a == 0))
       : \sum_(b <- s1) C b *: B b - C a *: B a = \sum_(b <- undup (a :: s1))  (funOneMinus s1 C a b) *: B b.
      Proof. rewrite/funOneMinus/=.
      case(a \in s1) as []eqn:E1.
        rewrite (undup_id U1) E1.
        destruct (in_cat E1) as [x1 [x2 S]].
        rewrite S !big_cat/= !big_seq1 eq_refl scale0r add0r
        (addrC (C a *: B a) _) -!addrA addrN addr0 -!big_cat/= !big_seq.
        apply eq_bigr=>i P.
        case(i == a) as []eqn:F=>//.
          move/eqP in F; rewrite F mem_cat in P.
          move/orP in P; destruct P as [P|P].
            rewrite S cat_uniq cat_uniq in U1; move: U1.
            rewrite -!(rwP andP)=> U1; destruct U1 as [_ [U1 _]].
            move/hasPn in U1.
            move:(mem_head a x2); rewrite -cat1s=>G.
            move:(U1 a G).
            by rewrite /=P.

            rewrite S cat_uniq cat_uniq in U1; move: U1.
            rewrite -!(rwP andP)=> U1; destruct U1 as [_ [_ [_ [U1 _]]]].
            move/hasPn in U1.
            move:(U1 a P).
            by rewrite /= mem_seq1 eq_refl.

        rewrite (undup_id U1) E1 big_cons eq_refl (rwP eqP) subr_eq addrC addrA scaleNr addrN add0r !big_seq -(rwP eqP).
        apply eq_bigr=>i P.
        case(i == a) as []eqn:F=>//.
        by move/eqP in F; rewrite -F P in E1.
      Qed.

      Lemma eqLCSumsTo (C : B -> R) s1 s2 : (hasSupport C s1) -> (hasSupport C s2)
      -> uniq s1 -> uniq s2
      -> \sum_(b <- s1)(C b) *: (B b) = \sum_(b <- s2)(C b) *: (B b).
      Proof.
        move:C s1.
        induction s2=>C s1 H1 H2 U1 U2.
        rewrite big_nil (rwP eqP).
        apply (zeroLCSumsTo H1 H2).
        simpl in U2; move/andP in U2.
        case(C a == 0) as []eqn:E.
        move: (fsFun.finSupp_cons H2 E)=>H2c.
        move/eqP in E.
        by rewrite big_cons (IHs2 C s1 H1 H2c U1 (proj2 U2)) E scale0r add0r.
        apply negbT in E.
        move: (IHs2 _ _ (fsOneMinusB H1 H2) (fsOneMinusA H1 H2) (undup_uniq _) (proj2 U2))=>H.
        rewrite big_cons (rwP eqP) addrC -subr_eq.

        by rewrite (RHSeq H1 H2 U1 (proj1 U2) (proj2 U2) E) -H
                   (LHSeq H1 H2 U1 (proj1 U2) (proj2 U2) E).
      Qed.
    End SumsTo.
  End Results.
  
  Section Add.
    Import Exports.
    Variable (R : ringType) (M : lmodType R) (B : lmodSetType M) (C D : type B).
    
    Lemma add_sumsTo m n : sumsTo C m -> sumsTo D n -> sumsTo (C <+> D) (m + n).
    Proof. move=>HM HN.
      destruct HM as [sm [Um [Hm Sm]]], HN as [sn [Un [Hn Sn]]].
      refine(ex_intro _ (undup (sm ++ sn)) (ex_intro _ (undup_uniq (sm ++ sn)) _)).
      
      have HS : hasSupport (C <+> D) (undup (sm ++ sn)).
      move=>b X. rewrite mem_undup mem_cat.
      rewrite /(fsFun.add _)/= in X.
      case(~~(C b == 0)) as []eqn:E.
      by rewrite (Hm _ E).
      move/negbFE/eqP in E.
      rewrite E add0r in X.
      by rewrite (Hn _ X) orbT.

      refine(ex_intro _ HS _).
      rewrite /(fsFun.add _)/=.
      under eq_bigr do rewrite GRing.scalerDl.
      rewrite big_split/=.
      rewrite (eqLCSumsTo _ (fsFun.hasSupport_undup (fsFun.hasSupport_catl sn Hm))) in Sm=>//; [|by apply undup_uniq].
      rewrite (eqLCSumsTo _ (fsFun.hasSupport_undup (fsFun.hasSupport_catr sm Hn))) in Sn=>//; [|by apply undup_uniq].
      move/eqP in Sm; move/eqP in Sn.
      by rewrite Sm Sn.
    Qed.
  End Add.

  Section Scale.
    Import Exports.
    Variable (R : ringType) (M : lmodType R) (B : lmodSetType M) (r : R) (C : type B).
    
    Lemma scale_sumsTo m : sumsTo C m -> sumsTo (r <*:> C) (r *: m).
    Proof. move=>H.
      destruct H as [x [Ux [Hx Sx]]].
      refine(ex_intro _ x _).
      refine(ex_intro _ Ux _).
      have HS :hasSupport (r <*:> C) x.
      move=>b X.
      rewrite /(fsFun.scale _)/= in X.
      case(~~(C b == 0)) as []eqn:E.
      apply (Hx _ E).
      move/negbFE/eqP in E.
      by rewrite E mulr0 eq_refl in X.

      refine(ex_intro _ HS _).
      rewrite /(fsFun.scale _)/=.
      under eq_bigr do rewrite -scalerA.
      move/eqP in Sx.
      by rewrite -scaler_sumr Sx.
    Qed.
  End Scale.



  Section Sums.
    Import Exports.
      Variable (R : ringType)(M1 : lmodType R) (M2 : lmodType R)
      (B1 : lmodSetType M1) (B2 : lmodSetType M2).

      Section Def.
        Variable (C1 : type B1) (C2 : type B2).
        Definition sum : type (lmodSet.sum B1 B2) := fsFun.sum C1 C2.
      End Def.

      Section Result.
        Variable (C1 : type B1) (C2 : type B2).

        Lemma hasFunSupp_sum s1 s2 : hasSupport C1 s1 -> hasSupport C2 s2
          -> hasSupport (C1 <\oplus> C2) (fsFun.sum_seq s1 s2).
          Proof.  move=>H1 H2 b C.
            rewrite mem_cat.
            destruct b.
            move: (H1 _ C)=>D1.
            apply (map_f (@inl B1 B2)) in D1.
            by rewrite D1.
            move: (H2 _ C)=>D2.
            apply (map_f (@inr B1 B2)) in D2.
            by rewrite D2 orbT.
          Qed.
    End Result.
  End Sums.

  Section Results.
    Variable (R : ringType) (M : lmodType R) (B : lmodSetType M).

    Lemma sumToElem_sumToZero (C : type B) (b : B) : sumsTo C (B b) ->  sumsTo (C <+> unitFSType b (-1)) 0.
    Proof. move=>Z.
      move:(add_sumsTo Z (unit_sumsTo b (-1%R))).
      by rewrite scaleNr scale1r addrN.
    Qed.
  End Results.

End lmodLC.
Export lmodLC.Exports.

Notation lmodLCSumsTo := lmodLC.sumsTo.
Notation eqLCSumsTo := lmodLC.eqLCSumsTo.