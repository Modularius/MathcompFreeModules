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
From mathcomp Require Import ssreflect ssrfun eqtype seq fintype finfun finset bigop matrix ring_quotient generic_quotient.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
  From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Modules Linears DirectSum Basis FreeModules RingIBN lmodLinearCombination FiniteSupport.

Open Scope lmod_scope.
Open Scope ring_scope.
Section Properties.
  Variable (R : ringType).
  Section Def.
    Variable (n m : nat).

  Definition split_fmod_raw
    : {linear R\lmod^(n + m) -> R\lmod^n \oplus R\lmod^m}
    := \colmap(lsubmx_linear _ _ n m, rsubmx_linear _ _ n m).

  Definition row1_raw := fun x : R\lmod^n => row_mx x (0 : 'M_(_,m)).
  Definition row2_raw := fun x : R\lmod^m => row_mx (0 : 'M_(_,n)) x.
  Lemma row1_lin : linear row1_raw.
  Proof. rewrite /row1_raw=>r x y.
    by rewrite scale_row_mx scaler0 add_row_mx addr0. Qed.
  Lemma row2_lin : linear row2_raw.
  Proof. rewrite /row2_raw=>r x y.
    by rewrite scale_row_mx scaler0 add_row_mx addr0. Qed.
  Definition unsplit_fmod_raw
    : {linear R\lmod^n \oplus R\lmod^m -> R\lmod^(n + m)}
    := \rowmap(Linear row1_lin, Linear row2_lin).
  
  Lemma split_fmod_lin : linear split_fmod_raw /\ linear unsplit_fmod_raw.
  Proof. by split=>r x y; rewrite linearP. Qed.

  Lemma split_fmodK : cancel split_fmod_raw unsplit_fmod_raw /\ cancel unsplit_fmod_raw split_fmod_raw.
  Proof. split; simpl; rewrite/dsLmod.Pair.to_ds_raw/dsLmod.Pair.from_ds_raw=>x;
    [|rewrite {5}(dsLmod.Pair.inj_proj_sum x); destruct x];
    rewrite /row1_raw/row2_raw add_row_mx=>/=.
    by rewrite !addr0 !add0r hsubmxK.
    by rewrite row_mxKl row_mxKr addr0 add0r.
  Qed.
  
  Definition split_fmod := linIsomBuildPack split_fmod_lin split_fmodK.
  End Def.

  Section Lifts.
  Variable (n m : nat) (f : {linear R \lmod^m -> R \lmod^n})
  (g : {linear R \lmod^n -> R \lmod^m}) (Inj : cancel f g) (Sur : cancel g f).

  Section Lemmas2.
    Variable (X : m < n).

    (* Given a proof that m < n, we map a vector of
    R\lmod^n to R\lmod^(m + (n - m))
    via the identity *)
    Definition partition_dim_raw : R \lmod^n -> R \lmod^(m + (n - m)).
      rewrite addnBCA=>//.
      by rewrite subnn addn0.
      by rewrite leq_eqVlt X -(rwP orP); right.
    Defined.
    Definition unpartition_dim_raw : R \lmod^(m + (n - m)) -> R \lmod^n.
      rewrite addnBCA=>//.
      by rewrite subnn addn0.
      by rewrite leq_eqVlt X -(rwP orP); right.
    Defined.

    Lemma partition_dim_lin : linear partition_dim_raw /\ linear unpartition_dim_raw.
    Proof. split;
      rewrite/partition_dim_raw/unpartition_dim_raw/eq_rect_r/eq_rect=>r x y/=;
      by destruct(Logic.eq_sym _), (Logic.eq_sym _), (Logic.eq_sym _).
    Qed.
    Lemma partition_dimK : cancel partition_dim_raw unpartition_dim_raw /\ cancel unpartition_dim_raw partition_dim_raw.
      Proof. split; simpl; rewrite /partition_dim_raw/unpartition_dim_raw/eq_rect_r/eq_rect=>x/=;
      by destruct(Logic.eq_sym _), (Logic.eq_sym _), (Logic.eq_sym _).
    Qed.

    Definition partition_dim := linIsomBuildPack partition_dim_lin partition_dimK.
    Definition split_vs := linIsomConcat partition_dim (@split_fmod m (n - m)).

    Definition extend_f : {linear R\lmod^n -> R\lmod^n}
     := f \oLin (dsLmod.Pair.proj1 _ _) \oLin split_vs.

    Definition extend_g : {linear R\lmod^n -> R\lmod^n}
     := inv(split_vs) \oLin (dsLmod.Pair.inj1 _ (R\lmod^(n - m)) \oLin g).
  
    Lemma extend_fgK : cancel extend_g extend_f.
    Proof. by rewrite/extend_f/extend_g=>x;
      rewrite -!linCompChain (isomKl split_vs) Sur.
    Qed.
    End Lemmas2.
  End Lifts.
End Properties.


(*        
Open Scope ring_scope.
Module ringIBN.
  Section Def.
    Definition axiom (R : ringType) :=
      forall n m : nat,
        (linIsomType (R\lmod^n) (R\lmod^m)) -> n == m.

    Record mixin (R : ringType) := Mixin { _ : axiom R; }.
    Record type := Pack { sort : _;  class_of : mixin sort; }.
    End Def.
    Open Scope quotient_scope.
    Section Result.
      Variable (R : comRingType) (I : {pred R})
      (idealI : idealr I) (kI : keyed_pred idealI).

      Definition qr := Quotient.rquot_ringType kI.

      Theorem ideal_IBN_implies_IBN : axiom qr -> axiom R.
      Proof. rewrite /axiom=>H n m psi.
      Check fun r => fdBasis (qr \lmod^ r).
    End Result.
*)
(*

        Definition nonsingular (h : {linear R\lmod^n -> R\lmod^n})
        := forall x, h x = 0 -> x = 0.

        Lemma nonsingularE (h : {linear R\lmod^n -> R\lmod^n})
        : nonsingular h -> (forall y, {x : R\lmod^n | h x == y}).
        Proof.
          rewrite/nonsingular=>H y.
        Admitted.
        Lemma nonsingular_nonzero_det (h : {linear R\lmod^n -> R\lmod^n})
         : nonsingular h -> \det(lin1_mx h) != 0.
        Proof. rewrite/nonsingular-(rwP negP)/not=>H.
          rewrite -(rwP det0P) => N.
          destruct N.
          rewrite mul_rV_lin1 /to_map  in H1.
          by rewrite (H x H1) eq_refl in H0.
          (*have: h (from_row (ringPowerOfSize R n) x) = 0.
          have: from_row (ringPowerOfSize R n) (to_row (M:=R \lmod^ n) (ringPowerOfSize R n)
          (h (from_row (M:=R \lmod^ n) (ringPowerOfSize R n) x))) = 0.
          by rewrite H1 linear0.
          move=>J.
          by rewrite tofrom_rowK in J.
          move=>J.
          assert(J2 := H (from_row (ringPowerOfSize R n) x) J).
          assert(J3 : to_row (ringPowerOfSize R n) (from_row (ringPowerOfSize R n) x) = 0).
          by rewrite J2 linear0.
          rewrite fromto_rowK in J3.
          by rewrite J3 eq_refl in H0.*)
        Qed.

        Definition nonsingular_inverse_raw
        (h : {linear R\lmod^n -> R\lmod^n}) : R\lmod^n -> R\lmod^n
           := fun x => (mulmx x (invmx (lin1_mx h))).
        Lemma nonsingular_inverse_lin (h : {linear R\lmod^n -> R\lmod^n})
          : linear (nonsingular_inverse_raw h).
          Proof. rewrite/nonsingular_inverse_raw=>r x y.
          by rewrite mulmxDl scalemxAl. Qed.
        Definition nonsingular_inverse
        (h : {linear R\lmod^n -> R\lmod^n}) : {linear R\lmod^n -> R\lmod^n}
            := Linear (nonsingular_inverse_lin h).

        Lemma nonsingular_bijective (h : {linear R\lmod^n -> R\lmod^n})
        : nonsingular h -> bijective h.
        Proof.
          move=>N.
          Admitted.

        Lemma nonsingular_product1 (h1 h2 : {linear R\lmod^n -> R\lmod^n})
        : nonsingular (h2 \oLin h1) -> nonsingular h1.
        Proof. rewrite/nonsingular=>/=X x Z.
              (have: (h2 (h1 x)) = 0 by rewrite Z linear0)=>H.
              rewrite linCompChain in H.
              by apply (X x H).
        Qed.

        Lemma nonsingular_products (h1 h2 : {linear R\lmod^n -> R\lmod^n})
        : nonsingular h1 /\ nonsingular h2 -> nonsingular (h2 \oLin h1).
        Proof.
          rewrite/nonsingular=>/=X.
          move=>x H; destruct X as [X1 X2].
          rewrite -linCompChain in H.
          by apply (X1 x (X2 (h1 x) H)).
        Qed.

        Lemma nonsingular_product_sym (h1 h2 : {linear R\lmod^n -> R\lmod^n})
        : nonsingular (h2 \oLin h1) -> nonsingular (h1 \oLin h2).
        Proof. move=>H. apply nonsingular_products. split; [| by apply (nonsingular_product1 H)]. rewrite/nonsingular.
          move:(nonsingular_product1 H)=>H1.
          rewrite/nonsingular in H H1.
          move: (nonsingular_product1 N); rewrite/nonsingular=>N1.
          have N2: forall x : R \lmod^ n, h2 x = 0 -> x = 0.
          move=>x H2.
          move:(N1 (h2 x))=>H12.
          rewrite linCompChain in H12.
        Lemma nonsingular_product (h1 h2 : {linear R\lmod^n -> R\lmod^n})
        : nonsingular (h2 \oLin h1) <-> nonsingular h1 /\ nonsingular h2.
        Proof. split; rewrite/nonsingular=>/=X. {
            split=>x Z. {
              (have: (h2 (h1 x)) = 0 by rewrite Z linear0)=>H.
              rewrite linCompChain in H.
              by apply (X x H).
            }
            (have: nonsingular h1 by
              rewrite/nonsingular=>x0 H;
              (have: h2 (h1 x0) = 0 by rewrite H linear0)=>H2;
              rewrite linCompChain in H2;
              by apply (X x0 H2));
            rewrite/nonsingular=>H.
            destruct (nonsingular_bijective H).
            (have : h2 (h1 (g0 x)) = 0 by rewrite H1)=>H2.
            rewrite linCompChain in H2.
            assert(P := X (g0 x) H2).
            apply (f_equal h1) in P.
            by rewrite H1 linear0 in P.
          }
          move=>x H; destruct X as [X1 X2].
          rewrite -linCompChain in H.
          by apply (X1 x (X2 (h1 x) H)).
        Qed.
Check \det (lin1_mx (extend_g _)) = 0.

      Lemma detEX_fg_one X : \det (lin1_mx ((extend_f X) \oLin (extend_g X))) = 1.
      have H:
      lin1_mx ((extend_f X) \oLin (extend_g X)) = lin1_mx (extend_f X) *m (lin1_mx (extend_g X)).
      rewrite -matrixP=>i j.
      rewrite mxE  /extend_g/extend_f -!linCompChain (isomKl (split_vs _)) (dsLmod.Pair.proj1_inj1K _ _) Sur.
      rewrite mxE mxE.
      rewrite /split_vs.
      Lemma detEx_f H : \det (lin1_mx (extend_g H)) = 0.
      Proof. rewrite /extend_g.

      Lemma L1 : ~~(m < n).
      Proof. apply(rwP negP); rewrite/not=>X.
        (have:(0 < n - m) by
          induction n; [inversion X|rewrite subn_gt0])=>H.
        have N: nonsingular ((extend_f X) \oLin (extend_g X)) by move=>x L;
        rewrite -linCompChain (extend_fgK X x) in L.
        rewrite /nonsingular in N.
        (*rewrite nonsingular_product=>K; destruct K as [_ K2].*)

        have V: extend_f X (inv(split_vs X) (dsLmod.Pair.inj2 (R\lmod^m) _ (const_mx 1))) = 0
          by rewrite /extend_f -!linCompChain (isomKl (split_vs _))
          dsLmod.Pair.proj1_inj20 linear0.
        rewrite /extend_f -!linCompChain in V.
        apply (f_equal g) in V.
        rewrite Inj (isomKl (split_vs _)) dsLmod.Pair.proj1_inj20
        !linear0 in V.
        move:(K2 _ V)=>E.
        apply (f_equal (split_vs X)) in V.
        apply (f_equal (dsLmod.Pair.proj2 _ _)) in E; move: E.
        rewrite (isomKl (split_vs _)) dsLmod.Pair.proj2_inj2K
        !linear0 /(GRing.zero _) -matrixP /eqrel=>E.
        move: (E (Ordinal (ltnSn 0)) (Ordinal H)).
        by rewrite !mxE (rwP eqP) oner_eq0.
      Qed.


      Lemma L2 : ~~(n < m).
        apply(rwP negP); rewrite/not=>X.
        (have:(0 < m - n) by induction n=>//;
          [inversion X; rewrite subn0|rewrite subn_gt0])=>H.
      Admitted.
      End Lemmas.
      End Result.

        Section Def.
        Variable (R : comRingType).
    Lemma cRingIBN : axiom R.
    Proof. move=>n m E.
      move:(L1 (isomlK E) (isomKl E)) (L2 (isomlK E) (isomKl E)).
      by rewrite -!leqNgt eqn_leq -(rwP andP).
    Qed.

    Definition cRingToRingIBN : type := Pack (Mixin cRingIBN).
  End Def.

  Module Exports.
    Notation ringIBNType := type.
    Coercion sort : type >-> ringType.
    Coercion class_of : type >-> mixin.
    Notation cRingToRingIBN := cRingToRingIBN.
    Coercion cRingToRingIBN : comRingType >-> type.
  End Exports.
End ringIBN.
Export ringIBN.Exports.

*)


Module fdFreeLmodDimension.
  Section Def.
  Definition dim {R : ringIBNType} (M : fdFreeLmodType R) : nat
    := lmodFinBasis.basis_number (fdBasis M).
  End Def.

  Section Theory.
    Variable (R : ringIBNType).
    
    Section ExchangeLemma.
    Variable (M : lmodType R) (F : lmodFinSetType M).
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
            move: (D1 a);clear D1.
            case(~~(C a == 0%R)) as []eqn:K.
            rewrite mem_cat E orbF=>D1.
            by rewrite (D1 is_true_true)/= in U1; destruct U1.
            move/negbFE in K=>_.
          admit.
      Admitted.
    End ExchangeLemma.

    Variable (M : lmodType R) (B1 B2 : lmodFinBasisType M).
(*    Definition sumOfB1B2_elem (b : B1 + B2) := match b with inl b' => B1 b'|inr b' => B2 b' end.
    Lemma sumOfB1B2_inj : injective sumOfB1B2_elem.
    Proof.
      rewrite/sumOfB1B2_elem=>x y.
      destruct x, y=>H.
      by move:(typeIsInjective H)=>D; destruct D.
    Definition sumOfB1B2 : lmodSetType M := lmodSet.Pack (lmodSet.Mixin B2).*)

    Definition n1 := (size (enum (to_FinType B1))).
    Definition n2 := (size (enum (to_FinType B2))).
    Notation mx := (maxn n1 n2).
    

    Notation E1 := (erefl n1).
    Notation E2 := (erefl n2).

    Notation M1 := (erefl (size (enum (fdBasis (fdFreeLmodPack B1))))).
    Notation M2 := (erefl (size (enum (fdBasis (fdFreeLmodPack B2))))).

    Notation f1 := (freeLinear.to_row M1).
    Notation f2 := (freeLinear.to_row M2).
    Section Contradiction.
      Variable (X1 : n1 < mx) (X2 : n2 < mx).
      Definition r1 := inv(partition_dim _ X1) \oLin inv(split_fmod _ _ _) \oLin \colmap(f1,\0_(_,R\lmod^(mx - n1))).
      Definition r2 := inv(partition_dim _ X2) \oLin inv(split_fmod _ _ _) \oLin \colmap(f2,\0_(_,R\lmod^(mx - n2))).
    
      Definition trans1 (i : 'I_(n1 + (mx - n1))) : 'I_mx.
        rewrite addnC subnK in i;[by unfold mx|apply leq_maxl].
      Defined.
      Definition trans2 (i : 'I_(n2 + (mx - n2))) : 'I_mx.
        rewrite addnC subnK in i; [by unfold mx | apply leq_maxr].
      Defined.
      Definition detrans1 (i : 'I_mx) : 'I_(n1 + (mx - n1)).
        rewrite addnC subnK;[by unfold mx in i|apply leq_maxl].
      Defined.
      Definition detrans2 (i : 'I_mx) : ('I_(n2 + (mx - n2))).
        rewrite addnC subnK; [by unfold mx in i | apply leq_maxr].
      Defined.


      Lemma trans1_inj : injective trans1.
      Proof. rewrite /trans1/eq_rect_r/eq_rect/==>x y.
        by destruct (Logic.eq_sym _); destruct (Logic.eq_sym _).
      Qed.
      Lemma trans2_inj : injective trans2.
      Proof. rewrite /trans2/eq_rect_r/eq_rect/==>x y.
        by destruct (Logic.eq_sym _); destruct (Logic.eq_sym _).
      Qed.

      Definition seq1 := map (trans1 \o (lshift (mx - n1)) \o (finBasis_to_ord E1)) (enum B1).
      Definition seq2 := map (trans2 \o (lshift (mx - n2)) \o (finBasis_to_ord E2)) (enum B2).

      Lemma uniq_seq : uniq seq1 /\ uniq seq2.
      Proof. split; rewrite/seq1/seq2 map_inj_in_uniq; [apply enum_uniq| |apply enum_uniq|];
        move=>x y X Y;
        rewrite/comp=>H;
        [move/trans1_inj/lshift_inj/(f_equal (ord_to_finBasis M1)) in H|
         move/trans2_inj/lshift_inj/(f_equal (ord_to_finBasis M2)) in H];
        by rewrite !ord_to_finBasisK in H.
      Qed.

      Definition set_concat := (map B1 (enum B1)) ++ (map B2 (enum B2)).
      Lemma set_nondeg : all (fun m => ~~ (m == 0)) set_concat.
      Proof.
        rewrite -(rwP allP)=>m X.
        by rewrite mem_cat in X; move/orP in X; destruct X as [X|X];
        move/mapP in X; destruct X as [b Y E]; rewrite E;
        move:(typeIsNonDegenerate b).
      Qed.
      Definition set := lmodFinSet.seq set_nondeg.
      Lemma B1_inSet b : B1 b \in set_concat.
      Proof. rewrite /set_concat mem_cat -(rwP orP)-(rwP mapP); left.
        refine(ex_intro2 _ _ b _ _)=>//.
        by rewrite mem_enum.
      Qed.
      Lemma B2_inSet b : B2 b \in set_concat.
      Proof. rewrite /set_concat mem_cat -(rwP orP)-(rwP (mapP (T1:=B2))); right.
        refine(ex_intro2 _ _ b _ _)=>//.
        by rewrite mem_enum.
      Qed.

      Definition seq_1 := map (fun b => SeqSub (B1_inSet b)) (enum B1).
      Definition seq_2 := map (fun b => SeqSub (B2_inSet b)) (enum B2).
      Definition fn1 (coef : set -> R) := (fun b : B1 => coef (SeqSub (B1_inSet b))).

      Lemma HSfn1 coef : hasSupport (fn1 coef) (enum B1).
      Proof. by move=>a X; by rewrite mem_enum. Qed.
      Lemma FSEfn1 coef : fsFun.finSuppE (fn1 coef).
      Proof. apply(ex_intro _ (enum B1) (ex_intro _ (enum_uniq B1) (@HSfn1 coef))). Qed.

      Lemma LI_1 : seq_li (F := set) seq_1.
      Proof.
        move=>C H S.
        have SM : lmodLCSumsTo (fsFun.Pack (FSEfn1 C)) 0.
        destruct S as [ss [sU [sH sS]]].
        refine(ex_intro _ (enum B1) (ex_intro _ (enum_uniq B1) _))=>/=.
        refine(ex_intro _ (@HSfn1 C) _ ).
        rewrite(lmodLC.finSuppsSumToEq sH H sU)/seq_1 in sS.
        rewrite big_map/set/= in sS.
        by rewrite /fn1.
        rewrite map_inj_in_uniq.
        apply enum_uniq.
        move=>x y X Y V.
        inversion V.
        apply (typeIsInjective H1).
        move:(lmodBasis.hasLI (B:=B1) (C:=fsFun.Pack (FSEfn1 C)) SM).
        rewrite !fsFun.eqFSFun/=/fn1=>D.
        apply functional_extensionality=>b.
        destruct b as [b B].
        assert(B' := B).
        unfold set_concat in B'.
        rewrite mem_cat in B'.
        move/orP in B'.

        rewrite /set/=/lmodFinSet.elem_seq/= in sS.
        simpl.
        
        Check lmodBasis.hasLI .

      
      Theorem invariant_dimension
        : basis_number B1 == basis_number B2.
      Proof.

      have LI: seq_li (F := set) seq_1.
          move=>C _ S.
          unfold set in C; simpl in C.
          unfold set in S; simpl in S.
          destruct S as [s [U [H S]]].
          have: fsFun.hasSupp C (enum B1).
          have: lmodLC.sumsTo 5.
          rewrite /set/=/lmodFinSet.elem_seq/ssval in S.
          unfold set in s; simpl in s.
          move:s U H S.
          rewrite (seq_subE 5).
          unfold set_concat in s; simpl in s.
         move:(freeLmodVector.fn_li S).
        move:(@steinitz_exchange (R\lmod^_) (freeLmodVector.basis R _) seq1 seq2 (proj1 uniq_seq) (proj2 uniq_seq) LI).


      have SP: seq_span (F:=freeLmodVector.basis R _) seq2.
      move=>m.
      destruct(@freeLmodVector.fn_spanning R mx m) as [C H].
      refine(ex_intro _ C _)=>b; split.
      rewrite /seq2 map_comp=>B.
      rewrite -(rwP mapP).
      destruct((split \o detrans2) b) as []eqn:E.
      refine(ex_intro2 _ _ o _ _).
      rewrite -(rwP mapP).
      refine(ex_intro2 _ _ (ord_to_finBasis E2 o) _ _).
      admit.
      by rewrite finBasis_to_ordK.
      destruct o.
      induction m0.
      simpl in E.
      simpl.
      inversion E.

      destruct (enum_val).
      move=>m.
      refine(ex_intro _ (lmodBasis.hasSpanLC (dsFdFreeLmod.Pair.basis B1 B2) m) _)=>b.
      split; [|apply (lmodBasis.hasSpanEq (dsFdFreeLmod.Pair.basis B1 B2) m)]. move=>X.
      destruct b.
      rewrite /lmodBasis.hasSpanLC/dsFdFreeLmod.Pair.basis/= in X.
      destruct(dsFdFreeLmod.Pair.pair_sp) as [C S].
      destruct S as [o [U [H S]]].
      simpl in X.
      Check (H _ X).
      simpl in X.
      rewrite -(rwP mapP).
      destruct B2 as [B2 T], B2 as [B2 T'].
      simpl. simpl in X, b, LI.
      by rewrite (mem_enum B2 b).
      by apply (lmodBasis.hasSpanEq B2 m).

      rewrite /basis_number cardT cardT eqn_leq.
    Admitted.

      move:(@steinitz_exchange lmodSet).

      simpl in b.
      by [].
      Print Mem.
      apply (Mem ).
      destruct
      rewrite 
    rewrite .
    by rewrite -(rwP andP); split;
      [ apply (steinitz_exchange B1 B2) | apply (steinitz_exchange B2 B1) ].
    Qed.
(*
    Axiom rank_nullity : forall {M N : fdFreeLmodType R} (f : {linear M -> N}),
      (dim (fdSubLmod \image(f))) + (dim (fdSubLmod \ker(f))) == (dim M).
*)
    Lemma dim_of_DSPair : forall (M1 M2 : fdFreeLmodType R),
      dim (M1 \foplus M2) = (dim M1 + dim M2).
    Proof. move=> M1 M2.
      by rewrite /dsFdFreeLmod.Pair.fdFreeLmod/dim/basis_number card_sum.
    Qed.

    Lemma dim_of_DS : forall {F : finType} (I : F -> fdFreeLmodType R),
      dim (\fbigoplus I) = \sum_f (dim (I f)).
    Proof. move => F I.
      rewrite /dsFdFreeLmod.type/dsFdFreeLmod.Seq.fdFreeLmod -big_enum enumT =>/=.
      induction(Finite.enum F); by [
      rewrite /dim/basis_number big_nil card_void|
      rewrite big_cons -IHl -dim_of_DSPair /dsFdFreeLmod.Pair.fdFreeLmod/dsFdFreeLmod.Seq.basis].
    Qed.

(*
    Axiom dim_of_Quot : forall {M : fdFreeLmodType R} (S : subLmodType M),
      dim (fdSubLmod S) + dim (fdQuotLmod S) == dim M.
*)
    Close Scope nat_scope.
  End Theory.

  Module Exports.
    Notation "'\' 'dim' '(' M ')'" := (dim M) (at level 0, format "'\' 'dim' '(' M ')'") : lmod_scope.
  End Exports.
End fdFreeLmodDimension.
Export fdFreeLmodDimension.Exports.
Close Scope ring_scope.
Close Scope lmod_scope.