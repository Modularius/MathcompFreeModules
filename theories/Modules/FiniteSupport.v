(******************************************************************************)
(* Dr Daniel Kirk (c) 2021                                                    *)
(******************************************************************************)
(* Let R : ringType and B : eqType                                            *)
(******************************************************************************)
(* hasSupport f s == propositions stating that (s : seq B) contains at        *)
(*                       least the support of (f : B -> R), that is           *)
(*                       forall b : B, ~~(f b == 0) -> b \in s                *)
(*    finSuppE f  == an existential proposition guaranteeing the              *)
(*                       existance of a duplicate-free sequence of B          *)
(*                       containing the support of (f : B -> R), that is      *)
(*                       the support of (f : B -> R), that is                 *)
(*                       exists (s : seq B) (_ : uniq B), hasSupport f s      *)
(*    FSType B    == a record consisting of a function (sort : B -> R),       *)
(*                       and a proof of finSuppE sort                         *)
(*  nullFSType B  == the null function with trivial finite support            *)
(* unitFSType b r == the function with one non-trivial value, that is b |-> r *)
(*                   and b' |-> 0 for all b' != b                             *)
(******************************************************************************)
(* Let s1 s2 : seq B                                                          *)
(******************************************************************************)
(* hasSupport_catl s1 s2 == hasSupport f s1 -> hasSupport f (s1 ++ s2)        *)
(* hasSupport_catl s1 s2 == hasSupport f s2 -> hasSupport f (s1 ++ s2)        *)
(* hasSupport_undup s1   == hasSupport f s1 -> hasSupport f (undup s1)        *)
(******************************************************************************)
(* Let r : R and C D : FSType B                                               *)
(******************************************************************************)
(*   C <+> D    == the FSType that results from adding the underlying         *)
(*                 component-wise                                             *)
(*   r <*:> C   == the FSType that results from adding the underlying         *)
(*                 function component-wise                                    *)
(* C <\oplus> D == the FSType (B + B) that results from constructing the      *)
(*                 disjoint sum of C and D                                    *)
(*  eqFSFun C D == a lemma giving the equivance of C = D as FSTypes and as    *)
(*                 functions. Often used along with functional_extensionality *)
(******************************************************************************)


Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From mathcomp Require Import ssreflect ssrfun eqtype fintype seq bigop.

Require Import Modules Linears.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Import GRing.

Module fsFun.
  Section Def.
    Variable (R : ringType) (B : eqType).

    Definition hasSupport (f : B -> R) (s : seq B) := forall b : B, (f b != 0) -> (b \in s).
    Definition finSuppE (f : B -> R) := exists (s : seq B), uniq s /\ hasSupport f s.
    Record type := Pack {
      sort : B -> R;
      hasFiniteSupport : finSuppE sort;
    }.

    Lemma eqFSFun (C D : type) : C = D <-> (sort C) = (sort D).
    Proof. split; destruct C, D=>/=H. by inversion H.
    by destruct H; rewrite (proof_irrelevance _ hasFiniteSupport0 hasFiniteSupport1).
    Qed.
  End Def.
  
  Module Exports.
    Notation FSType := type.
    Coercion sort : type >-> Funclass.
  End Exports.

  Section Null.
    Variable (R : ringType) (B : eqType).

    Lemma null_finSuppE : finSuppE (fun _ : B => 0 : R).
    Proof. rewrite/finSuppE.
      refine(ex_intro _ nil _); split=>//.
      by rewrite/hasSupport eq_refl/=.
    Qed.

    Definition null := Pack (null_finSuppE).
  End Null.

  Section Singleton.
    Variable (R : ringType) (B : eqType)
      (b : B) (r : R).

    Lemma unit_finSuppE : finSuppE (fun b' : B => if b' == b then r else 0).
    Proof. rewrite/finSuppE.
      refine(ex_intro _ [::b] _); split=>//.
      rewrite/hasSupport =>b'.
      case (b' == b) as []eqn:E.
      move/eqP in E; destruct E.
      by rewrite in_cons eq_refl orTb.
      by rewrite eq_refl.
    Qed.

    Definition unit := Pack (unit_finSuppE).
  End Singleton.


  Section Results.
    Variable (R : ringType) (B : eqType).
    Import Exports.
    Section FiniteSupports.
      Variable (C : B -> R).
      Lemma hasSupport_catl s1 s2 : hasSupport C s1 -> hasSupport C (s1 ++ s2).
      Proof. rewrite/hasSupport=>H b F.
        by rewrite mem_cat (H b F). Qed.

      Lemma hasSupport_catr s1 s2 : hasSupport C s2 -> hasSupport C (s1 ++ s2).
      Proof. rewrite/hasSupport=>H b F.
        by rewrite mem_cat (H b F) orbT. Qed.
      
      Lemma hasSupport_undup s : hasSupport C s -> hasSupport C (undup s).
      Proof. rewrite /hasSupport=>H b F.
        by rewrite mem_undup; move: H b F. Qed.
      
      Lemma hasSupport_perm_eq s1 s2 : (perm_eq s1 s2) -> hasSupport C s1 -> hasSupport C s2.
      Proof. rewrite /hasSupport=>E H b F.
        apply perm_mem in E; rewrite -(E b); apply (H b F).
      Qed.

      Lemma finSupp_cons a s : hasSupport C (a :: s) -> (C a == 0) -> (hasSupport C s).
      Proof. rewrite /hasSupport=>F.
        case (~~(C a == 0)) as []eqn:E=>G.
        by rewrite G in E.
        move=>b V.
        move:(F b V); rewrite in_cons -(rwP orP)=>W.
        destruct W=>//.
        move/eqP in H; destruct H.
        by rewrite G in V.
      Qed.
    End FiniteSupports.
  End Results.


  Section Equality.
    Variable (R : ringType) (B : eqType).
    Import Exports.
    Lemma eqFSSupp (C D : type R B) : C = D <-> exists cd (Ec : hasSupport C cd) (Ed : hasSupport D cd), all (fun b => C b == D b) cd.
    Proof.
      split. destruct C as [c [cs [Uc C]]], D as [d [ds [Ud D]]]=>/=H.
      refine(ex_intro _ (undup(cs ++ ds)) _).
      inversion H; clear H.
      apply (hasSupport_catr cs) in D.
      apply (hasSupport_undup) in D.
      refine(ex_intro _ D _).
      refine(ex_intro _ D _).
      rewrite (eq_all (a2:=predT)).
      apply all_predT.
      by move=>b; rewrite eq_refl.

      move=>H; destruct H as [cd [fsC [fsD A]]].
      rewrite eqFSFun/=.
      apply functional_extensionality=>b.
      move/allP in A.
      case(~~(C b == 0)) as []eqn:Ec.
      move:(fsC _ Ec)=>inC.
      move:(A b inC)=>H.
      by move/eqP in H.
      case(~~(D b == 0)) as []eqn:Ed.
      move:(fsD _ Ed)=>inD.
      move:(A b inD)=>H.
      by move/eqP in H.
      move/negbFE/eqP in Ec.
      move/negbFE/eqP in Ed.
      by rewrite Ec Ed.
    Qed.
  End Equality.

  Section Add.
    Import Exports.
    Variable (R : ringType) (B : eqType) (C D : type R B).
    Lemma addFS : finSuppE (fun b => (C b) + (D b)).
    Proof. destruct C as [c [sc [CU CC]]], D as [d [sd [DU DD]]].
      refine(ex_intro _ (undup(sc ++ sd)) _); split; [apply(undup_uniq _)|].
      move: CC DD.
      rewrite/hasSupport/==> CC DD b H.
      case(~~(c b == 0)) as []eqn:E.
      by rewrite mem_undup mem_cat (CC b E) orTb.
      move/negbFE/eqP in E.
      rewrite E GRing.add0r in H.
      by rewrite mem_undup mem_cat (DD b H) orbT.
    Qed.

    Definition add : type R B := Pack addFS.
  End Add.

  Section Scale.
    Import Exports.
    Variable (R : ringType) (B : eqType) (r : R) (C : type R B).
    Lemma scaleFS : finSuppE (fun b => r * (C b)).
    Proof. destruct C as [c [sc [UC CC]]].
      refine(ex_intro _ sc _); split=>//.
      move: CC.
      rewrite/hasSupport/==> CC b H.
      case(~~(c b == 0)) as []eqn:E.
      by rewrite (CC b E).
      move/negbFE/eqP in E.
      by rewrite E GRing.mulr0 eq_refl in H.
    Qed.

    Definition scale : type R B := Pack scaleFS.
  End Scale.



  Section Sums.
    Import Exports.
      Variable (R : ringType) (B1 B2 : eqType).

      Section Def.
        Variable (C1 : type R B1) (C2 : type R B2).

        Definition sum_fn (b : B1 + B2)
         := match b with inl b' => sort C1 b' | inr b' => sort C2 b' end.

        Definition sum_seq (s1 : seq B1) (s2 : seq B2) := (map inl s1) ++ (map inr s2).

        Lemma sum_uniq s1 s2 (U1 : uniq s1) (U2 : uniq s2) : uniq (sum_seq s1 s2).
        Proof.
          rewrite -(map_inj_in_uniq (f:=@inl B1 B2)) in U1;[|by move=>x y _ _ H; inversion H].
          rewrite -(map_inj_in_uniq (f:=@inr B1 B2)) in U2;[|by move=>x y _ _ H; inversion H].
          rewrite cat_uniq U1 U2 andbT/=-(rwP hasPn)=>x X.
          destruct x.
          by move/mapP in X; destruct X.
          rewrite -(rwP negP)=>Y.
          by move/mapP in Y; destruct Y.
        Qed.

        Lemma sumFS : finSuppE sum_fn.
        Proof. rewrite/sum_fn.
          destruct C1 as [c1 [s1 [U1 S1]]], C2 as [c2 [s2 [U2 S2]]].
          refine(ex_intro _ (sum_seq s1 s2) _); split; [apply (sum_uniq U1 U2)|].
          move=>b C; destruct b.
          move:(S1 s C)=>D.
          apply (map_f (@inl B1 B2)) in D.
          by rewrite mem_cat D.
          move:(S2 s C)=>D.
          apply (map_f (@inr B1 B2)) in D.
          by rewrite mem_cat D orbT.
        Qed.

        Definition sum : type R (sum_eqType B1 B2) := Pack sumFS.
      End Def.

      Section Def.
        Variable (C : type R (sum_eqType B1 B2)).

        Definition foldL (c : seq (sum_eqType B1 B2)) : seq  B1
          := foldr (fun br (L : seq B1) => if br is inl br' 
            then br'::L else L) nil c.
        Lemma foldL_consl a (c : seq (sum_eqType B1 B2))
            : foldL ((inl a)::c) = a :: foldL c.
        Proof. by []. Qed.
        Lemma foldL_consr a (c : seq (sum_eqType B1 B2))
            : foldL ((inr a)::c) = foldL c.
        Proof. by []. Qed.

        Lemma subseql (c : seq (sum_eqType B1 B2)) :
          subseq (map (@inl B1 B2) (foldL c)) c.
        Proof. induction c=>//.
          destruct a; [rewrite foldL_consl| rewrite foldL_consr].
          by rewrite /=eq_refl IHc.
          apply (subseq_trans IHc (subseq_cons _ _)).
        Qed.

        Lemma foldL_uniq s : uniq s -> uniq (foldL s).
        Proof. move=>U.
          apply (subseq_uniq (subseql s)) in U.
          rewrite -(map_inj_in_uniq (f:=@inl B1 B2))=>//.
          move=>x y _ _ H; by inversion H.
        Qed.

        Lemma foldL_fs (c : sum_eqType B1 B2 -> R) s : hasSupport c s -> hasSupport (c \o inl) (foldL s).
        Proof. rewrite/comp=>S b B.
          move: (S (inl b) B); clear S.
          induction s=>//.
          rewrite in_cons -(rwP orP)=>X.
          destruct X.
          move/eqP in H.
          by rewrite -H foldL_consl in_cons eq_refl.
          destruct a.
          by rewrite foldL_consl in_cons (IHs H) orbT.
          by rewrite foldL_consr (IHs H).
        Qed.

        Lemma lsumFS : finSuppE (C \o inl).
        Proof. destruct C as [c [s [U S]]].
          refine(ex_intro _ (foldL s) _); split; [apply(foldL_uniq U)|apply(foldL_fs S)].
        Qed.

        Definition foldFSl := Pack lsumFS.

        Definition foldR (c : seq (sum_eqType B1 B2)) : seq  B2
          := foldr (fun br (L : seq B2) =>
        if br is inr br' then br'::L else L
          ) nil c.
        Lemma foldR_consr a (c : seq (sum_eqType B1 B2))
            : foldR ((inr a)::c) = a :: foldR c.
        Proof. by []. Qed.
        Lemma foldR_consl a (c : seq (sum_eqType B1 B2))
            : foldR ((inl a)::c) = foldR c.
        Proof. by []. Qed.

        Lemma subseqr (c : seq (sum_eqType B1 B2)) :
          subseq (map (@inr B1 B2) (foldR c)) c.
        Proof. induction c=>//.
          destruct a; [rewrite foldR_consl| rewrite foldR_consr].
          apply (subseq_trans IHc (subseq_cons _ _)).
          by rewrite /=eq_refl IHc.
        Qed.

        Lemma foldR_uniq s : uniq s -> uniq (foldR s).
        Proof. move=>U.
          apply (subseq_uniq (subseqr s)) in U.
          rewrite -(map_inj_in_uniq (f:=@inr B1 B2))=>//.
          move=>x y _ _ H; by inversion H.
        Qed.

        Lemma foldR_fs (c : sum_eqType B1 B2 -> R) s : hasSupport c s -> hasSupport (c \o inr) (foldR s).
        Proof. rewrite/comp=>S b B.
          move: (S (inr b) B); clear S.
          induction s=>//.
          rewrite in_cons -(rwP orP)=>X.
          destruct X.
          move/eqP in H.
          by rewrite -H foldR_consr in_cons eq_refl.
          destruct a.
          by rewrite foldR_consl (IHs H).
          by rewrite foldR_consr in_cons (IHs H) orbT.
        Qed.


        Lemma rsumFS : finSuppE (C \o inr).
        Proof. destruct C as [c [s [U S]]].
          refine(ex_intro _ (foldR s) _); split; [apply(foldR_uniq U)|apply(foldR_fs S)].
        Qed.

        Definition foldFSr := Pack rsumFS.
      End Def.
      Section Result.
        Variable (C1 : type R B1) (C2 : type R B2).

        Lemma hasFunSupp_sum s1 s2 : hasSupport C1 s1 -> hasSupport C2 s2
          -> hasSupport (sum C1 C2) (sum_seq s1 s2).
          Proof. 
            move=>H1 H2 b C.
            rewrite mem_cat.
            destruct b.
            simpl in C.
            move: (H1 _ C)=>D1.
            apply (map_f (@inl B1 B2)) in D1.
            by rewrite D1.
            simpl in C.
            move: (H2 _ C)=>D2.
            apply (map_f (@inr B1 B2)) in D2.
            by rewrite D2 orbT.
          Qed.
    End Result.
  End Sums.


End fsFun.
Export fsFun.Exports.
Notation hasSupport := fsFun.hasSupport.
Notation finSuppE := fsFun.finSuppE.
Notation nullFSType := fsFun.null.
Notation unitFSType := fsFun.unit.
Notation eqFSFun := fsFun.eqFSFun.
Infix "<+>" := fsFun.add (at level 39) : lmod_scope.
Infix "<*:>" := fsFun.scale (at level 39) : lmod_scope.
Infix "<\oplus>" := (fsFun.sum) (at level 39) : lmod_scope.
