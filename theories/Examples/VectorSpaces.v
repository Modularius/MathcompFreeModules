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
From mathcomp Require Import ssreflect ssrfun eqtype seq fintype bigop.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
  From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Modules Linears FiniteSupport lmodLC DirectSum Basis FreeModules RingIBN.

Open Scope lmod_scope.
Open Scope ring_scope.

Section FieldResult.
  Variable (K : fieldType).

  Section ExchangeLemma.
    Variable (M : lmodType K) (B : lmodSetType M).
    Lemma eqZero_eqElem (C : FSType K B) (b : B) : (C b != 0) -> lmodLCSumsTo C 0 ->
      lmodLCSumsTo (((-1/(C b)) <*:> C) <+> (unitFSType b 1)) (B b).
      move=>X S; move:(lmodLC.add_sumsTo (lmodLC.scale_sumsTo (-1/(C b)) S) (lmodLC.unit_sumsTo b 1)); clear S=>S.
      destruct S as [s [U [H S]]].
      refine(ex_intro _ s (ex_intro _ U (ex_intro _ H _))).
      by rewrite scaler0 add0r scale1r in S.
    Qed.
  End ExchangeLemma.

  Section ExchangeLemma.
    Variable (M : lmodType K) (F : lmodFinSetType M).
    Section Lemmas.
      Definition seq_li (s : seq F) := forall (C : lmodLCType F), hasSupport C s ->  lmodLC.li C.
      Definition seq_span (s : seq F) := forall m : M, exists C : lmodLCType F, hasSupport C s /\ lmodLC.sumsTo C m.

      Lemma seq_li_cons a (s : seq F) : seq_li (a::s) -> seq_li s.
      Proof. rewrite /seq_li/hasSupport=>H C B X.
        refine (H C _ X)=>b.
        rewrite in_cons=>Y.
        by rewrite (B b Y) orbT.
      Qed.


      Lemma seq_li_cons_span_false a (s : seq F) : (a \notin s) -> seq_li (a::s) -> seq_span s -> false.
      Proof. rewrite /seq_li/seq_span=>U H S.
        destruct (S (F a)) as [C SP]; clear S.
        destruct(SP) as [SP1 SP2]; clear SP.
        move:(lmodLC.add_sumsTo SP2 (lmodLC.unit_sumsTo a (-1%R)))=>G.
        rewrite scaleN1r addrN in G.
        have HS :hasSupport (C <+> unitFSType a (-1)) (a::s).
          move=>/=b B.
          case(b == a) as []eqn:E.
          by move/eqP in E; destruct E; rewrite in_cons eq_refl orTb.
          by rewrite addr0 in B; rewrite in_cons (SP1 _ B) orbT.
        move:(H (C <+> unitFSType a (-1)) HS G); clear H.
        rewrite fsFun.eqFSFun/==>H.
        move:(equal_f H a).
        rewrite eq_refl.
        case(C a == 0) as []eqn:E.
        by move/eqP in E; rewrite E (rwP eqP) subr_eq0 eq_sym oner_eq0.
        by move/negbT in E; rewrite (SP1 _ E)/= in U.
      Qed.
    End Lemmas.

    Open Scope nat_scope.
    Lemma steinitz_exchange (s1 s2 : seq F) (U1 : uniq s1) (U2 : uniq s2)
        (L : seq_li s1) (S : seq_span s2)  :
        (size s1 <= size s2) /\
        exists (s2' : seq F),
            subseq s2' s2  /\
            size s2' + size s1 == size s2 /\
            seq_span (s1 ++ s2').
    Proof.
      move:s2 U2 S.
      induction s1=>s2 U2 S; split=>//. (* induction and split creates 4 cases, the first of the base cases is solved trivially*)
        refine(ex_intro _ s2 _)=>/=.
        by rewrite subseq_refl addn0 eq_refl. (* solve second base case *)
        

        case(size (a :: s1) <= size s2) as []eqn:E=>//. (* solve by bool case, true case is solved trivially*)
        simpl in U1;move/andP in U1.
        move:(IHs1 (proj2 U1) (seq_li_cons L) s2 U2 S)=>N; destruct N as [N1 N2].
        move/negbT in E; simpl in E.
        rewrite -leqNgt in E.
        move:(eqn_leq (size s1) (size s2)).
        rewrite E N1/==>H.
        move/eqP in H.
        destruct N2 as [s2' [X [Y Z]]].
        destruct s2'. (* induct on size of s2' *)
        by rewrite cats0 in Z; apply (seq_li_cons_span_false (proj1 U1) L Z). (* size zero case solved *)
        rewrite H/=eq_sym in Y.
        move/eqP in Y.
        clear E H N1.
        induction (size s2); [by rewrite addn0 in Y|]; (* size nonzero case solved *)
        rewrite addSn in Y; inversion Y; rewrite addSnnS in IHn; apply(IHn H0).

        simpl in U1;move/andP in U1.
        destruct (IHs1 (proj2 U1) (seq_li_cons L) s2 U2 S) as [SIZE [s2' [SUBSEQ [SUBSIZE SUBSPAN]]]].

        case(a \in s2') as []eqn:E.
          move:(lmodLC.in_cat E)=>E2.
          destruct E2 as [e1 [e2 E2]].
          refine(ex_intro _ (e1 ++ e2) _).
          split. move:(cat_subseq (subseq_refl e1) (suffix_subseq [::a] e2))=>H.
          by rewrite -E2 in H; rewrite (subseq_trans H SUBSEQ).
          split. move/eqP in SUBSIZE.
          move:(f_equal size E2).
          rewrite /= size_cat/=size_cat/==>W.
          by rewrite -SUBSIZE W addnS addnS addSnnS addnS .
          move=>m.
          destruct(SUBSPAN m) as [C H].
          refine(ex_intro _ C _).
          split; [|apply (proj2 H)]=>b X.
          move: ((proj1 H) _ X); clear H.
          rewrite E2 -(cat1s a s1) !mem_cat=>H.
          move/orP in H; destruct H as [H|H].
          by rewrite H orbT.
          move/orP in H; destruct H as [H|H].
          by rewrite H orbT.
          move/orP in H; destruct H as [H|H].
          by rewrite H orTb.
          by rewrite H !orbT.

          destruct (SUBSPAN (F a)) as [C [D1 D2]].
          move: (D1 a);clear D1=>D1.
          apply (lmodLC.sumToElem_sumToZero) in D2.
          have Y:hasSupport (C <+> unitFSType (R:=K) (B:=F) a (-1)) (a :: s1).
          move=>b X.
          simpl in X.
          case(b == a) as []eqn:Eba. by move/eqP in Eba; rewrite Eba in_cons eq_refl orTb.
          rewrite Eba addr0 in X.
          destruct (S (F b)).
          move/(L _ _) in D2.
        admit.
    Admitted.
  End ExchangeLemma.



  Variable (M : lmodType K) (F : lmodFinSetType M).
  Export ringIBN.
  Theorem Fields_IBN : ringIBN.axiom K.
  Proof.
    rewrite IBN_equiv_equal_basis_nums=>V B1 B2.
  Admitted.
End FieldResult.
