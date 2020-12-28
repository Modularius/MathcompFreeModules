Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality ProofIrrelevance.
From mathcomp Require Import ssreflect ssrfun seq.
From mathcomp Require Import bigop eqtype choice fintype.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Modules FiniteSupport.
Open Scope ring_scope.
Open Scope lmod_scope.

Import GRing.
Module formalLC.
Section Def.
  Variable (R : ringType) (B : eqType).
  Definition sig_fn := forall C : FSType R B, {s : seq B | uniq s /\ fsFun.hasSupport C s}.
  Definition sig_fn_wd (span : sig_fn) := forall (C : B -> R) (E1 E2 : fsFun.finSuppE C),
    sval (span (fsFun.Pack E1)) = sval (span (fsFun.Pack E2)).
  Variable (span : sig_fn) (span_wd : sig_fn_wd span).

  Section Choice.
    Definition eqOp (x y : FSType R B) := all (fun b => x b == y b) (undup ((sval (span x)) ++ (sval (span y)))).
    Lemma eqAxiom: Equality.axiom eqOp.
    Proof. rewrite /eqOp=>x y; apply (iffP idP)=>H.
      rewrite fsFun.eqFSSupp/=.
      destruct(span x) as [xs [Ux Hx]], (span y) as [ys [Uy Hy]].
      refine(ex_intro _ (undup (xs ++ ys)) _); simpl in H.
      move/(fsFun.hasSupport_catl ys)/fsFun.hasSupport_undup in Hx.
      move/(fsFun.hasSupport_catr xs)/fsFun.hasSupport_undup in Hy.
      apply(ex_intro _ Hx (ex_intro _ Hy H)).

      rewrite -(rwP allP) H=>s _//.
    Qed.
    Definition lc_eqMixin := EqMixin eqAxiom.
    Definition lc_eqType := EqType (FSType R B) lc_eqMixin.

    Definition pr (P : pred lc_eqType) : pred B
     := fun b : B => P (unitFSType b 1).
    Definition lc_find (P : pred lc_eqType) (n : nat) : option (FSType R B).
    Admitted. (*
     := match Choice.find (Choice.mixin (Choice.class B)) (pr P) n with
     |Some t => Some (unitFSType t 1)
     |None => None
     end.*)

    Lemma lc_fin_correct : forall (P : pred lc_eqType) (n : nat) (x : lc_eqType),
      lc_find P n = Some x -> P x. Admitted. (*
      Proof. rewrite/lc_find=>P n x H.
        case(P x) as []eqn:E=>//.
        case(Choice.find (Choice.mixin (Choice.class B)) (pr P) n) as []eqn:C.
        move:(Choice.InternalTheory.correct C).
        rewrite/pr.
        inversion H.
        by rewrite H1 E.
        inversion H.
      Qed.*)
    Lemma lc_fin_complete (P : _ -> bool) : (exists x, P x) -> (exists n, lc_find P n).
    Proof.
      move=>X.
      destruct X.
      destruct x.
    Admitted.

    Lemma lc_fin_extensional (P Q : _ -> bool) : P =1 Q -> lc_find P =1 lc_find Q.
    Admitted.

    Definition lc_choiceMixin := Choice.Mixin lc_fin_correct lc_fin_complete lc_fin_extensional.
    Definition lc_choiceType := ChoiceType (lc_eqType) lc_choiceMixin.
  End Choice.
  Canonical lc_choiceType.

  Section Zmod.
    Definition Add (x1 x2 : FSType R B) := fsFun.add x1 x2.

    Definition Neg (x : FSType R B)
      := fsFun.scale (-1) x.

    Definition Zero := fsFun.null R B.

    Lemma addA : associative Add.
    Proof. rewrite/Add=>x y z; rewrite fsFun.eqFSFun/=;
      apply functional_extensionality=>p;
      by rewrite addrA. Qed.

    Lemma addC : commutative Add.
    Proof. rewrite/Add=>x y; rewrite fsFun.eqFSFun/=;
      apply functional_extensionality=>p;
      by rewrite addrC. Qed.

    Lemma left_id0 : left_id Zero Add.
    Proof. rewrite/Add/Zero=>x; rewrite fsFun.eqFSFun/=;
      apply functional_extensionality=>p;
      by rewrite add0r. Qed.

    Lemma right_id0 : right_id Zero Add.
    Proof. rewrite/Add/Zero=>x; rewrite fsFun.eqFSFun/=;
      apply functional_extensionality=>p.
      by rewrite addr0. Qed.

    Lemma left_inv0 : left_inverse Zero Neg Add.
    Proof. rewrite /Add/Neg/Zero=>x; rewrite fsFun.eqFSFun/=;
      apply functional_extensionality=>p;
      by rewrite mulN1r addNr. Qed.

    Lemma right_inv0 : right_inverse Zero Neg Add.
    Proof. rewrite /Add/Neg/Zero=>x; rewrite fsFun.eqFSFun/=;
      apply functional_extensionality=>p;
      by rewrite mulN1r addrN. Qed.

    Definition lc_zmodMixin := ZmodMixin addA addC left_id0 left_inv0.
    Definition lc_zmodType := ZmodType lc_choiceType lc_zmodMixin.
  End Zmod.

  Section Lmod.
    Definition Scale (r : R) (f : FSType R B) := fsFun.scale r f.

    Lemma scaleAxiom : forall (a b : R) (v : lc_zmodType),
      Scale a (Scale b v) = Scale (a * b) v.
    Proof. rewrite/Scale=> a b v;  rewrite fsFun.eqFSFun/=;
    apply functional_extensionality=>p.
    by rewrite mulrA.
    Qed.
    Lemma left_id_scale : left_id 1 Scale.
    Proof. rewrite/Scale=> a; rewrite fsFun.eqFSFun/=;
    apply functional_extensionality=>p.
    by rewrite mul1r.
    Qed.
    Lemma right_d_scale : right_distributive Scale Add.
    Proof. rewrite/Scale/Add=> r x y; rewrite fsFun.eqFSFun/=;
    apply functional_extensionality=>p.
    by rewrite mulrDr. Qed.

    Lemma lmodMorph : forall v : lc_zmodType,
      morphism_2 (Scale^~ v) (fun x y : R => x + y) (fun x y : lc_zmodType => x + y).
    Proof. rewrite/morphism_2/Scale/add=>f x y; rewrite fsFun.eqFSFun/=;
    rewrite/Add; apply functional_extensionality=>p;
    by rewrite mulrDl. Qed.

    Definition lc_lmodMixin := LmodMixin scaleAxiom left_id_scale right_d_scale lmodMorph.
    Definition lc_lmodType := LmodType R lc_zmodType lc_lmodMixin.
  End Lmod.
  Canonical lc_zmodType.
  Canonical lc_lmodType.

  Require Import lmodLC Basis FreeModules.
  Open Scope ring_scope.
  Section FreeLmod.
    Canonical lc_lmodType.

    Definition elem (p : B) : lc_lmodType := unitFSType p 1.

    Lemma elem_inj : @injective lc_lmodType _ elem.
    Proof. rewrite /elem=>x y; rewrite fsFun.eqFSFun/=.
      case (x == y) as []eqn:E=>H; [by apply (rwP eqP) in E | move: (equal_f H x)].
      by rewrite E eq_refl !(rwP eqP) (oner_eq0 R).
    Qed.

    Lemma elem_nondeg : @non_degenerate _ lc_lmodType _ elem.
    Proof. rewrite /elem=> x.
      apply (rwP negP); rewrite /not -(rwP eqP) fsFun.eqFSFun/==> H.
      by move: (equal_f H x); rewrite eq_refl (rwP eqP) (oner_eq0 R).
    Qed.

    Definition bset := lmodSet.Build elem_inj elem_nondeg.

      Section PathApply.
        Definition pathApply_raw (p : B) : lc_lmodType -> R := fun f => f p.

        Lemma pathApply_lin (p : B) : scalar (pathApply_raw p).
        Proof. by rewrite /(add _). Qed.

        Definition pathApply (p : bset) : {linear lc_lmodType -> R |*%R}
          := Linear (pathApply_lin p).
      End PathApply.


      Lemma li_ : lmodBasis.li bset.
      Proof. move=>H S; rewrite lmodLC.eqFSFun/=.
        apply functional_extensionality=>b.
        destruct H as [coefH H].
        destruct S as [s [Us [Hs S]]].
        move:H S Hs.
        rewrite /bset/=/elem.
        under eq_bigr do rewrite /(GRing.scale _)/=/Scale/fsFun.scale/=.
        move=>_ S Hs.
        move/eqP/(congr1 (pathApply b)) in S.
        rewrite linear_sum/= in S.
        
        case(~~(coefH b == 0)) as []eqn:E1.
        have E: forall i (_ : ~~ (i == b)), coefH i * (if b == i then 1 else 0) = if b == i then coefH i else 0
        by move=>i _; case (b == i);[rewrite mulr1|rewrite mulr0].
        rewrite (bigD1_seq b (Hs _ E1) Us)
        (eq_bigr _ E) -big_mkcondr/=eq_refl mulr1 big_pred0 in S; clear E.
        by rewrite addr0 in S.
        move=>i; case(i == b) as []eqn:Ei=>//; by rewrite eq_sym Ei.

        by move/negbFE/eqP in E1.
      Qed.

      Lemma span_ : lmodBasis.span bset.
        Proof. rewrite/lmodBasis.span=>m.
        move:(span m)=>[mys [myU myH]].

        have myFS: fsFun.hasSupport (fun b => if b \in mys then m b else 0) (undup mys).
        move=>b C.
        case (b \in mys) as []eqn:G.
        by rewrite mem_undup.
        by rewrite eq_refl in C.

        have myFSE: fsFun.finSuppE (fun b => if b \in mys then m b else 0) by
        apply (ex_intro _ _ (ex_intro _ (undup_uniq _) myFS)).

        refine(exist _ (fsFun.Pack myFSE) _).
        refine(ex_intro _ (undup mys) (ex_intro _ (undup_uniq _) _))=>/=.
        refine(ex_intro _ myFS _).

        destruct m as [fm [sm [Um Hm]]].
        simpl in myH, myFS, myFSE.
        rewrite -(rwP eqP) fsFun.eqFSFun/=.
        clear sm Um Hm.
        under eq_bigr do rewrite (@lmod_ifthenelse_sum _ _ _  _ _ (fun i => i \in _)) -mem_undup.
        rewrite -(big_mkcond (fun i => i \in undup mys) (fun i => fm i *: elem i))/=.
        clear myFS myFSE.
        move:fm myH.
        induction mys=>/=.
          move=>fm myH.
          apply functional_extensionality=>b.
          case(fm b == 0) as []eqn:E.
            move/eqP in E.
            by rewrite E big_nil.

            move/negbT in E.
            move:(myH _ E).
            by rewrite in_nil.

          move=>fm myH.
          case(a \in mys) as []eqn:E1.
            simpl in myU; by rewrite E1 in myU.

            apply functional_extensionality=>b.
            rewrite -big_seq big_cons (rwP eqP) eq_sym addrC -subr_eq eq_sym -(rwP eqP).
            
            have IH:  hasSupport
            (fun b : B => fm b - (if b == a then fm a else 0)) mys.
            move=>c X; case(c == a) as []eqn:Ec.
              by move/eqP in Ec; rewrite Ec addrN eq_refl in X.
              rewrite subr0 in X.

              case(fm a == 0) as []eqn:E2.
                simpl in myU; move/andP in myU.
                by apply (fsFun.finSupp_cons myH E2 X).

                by move:(myH _ X); rewrite in_cons Ec/=.

            simpl in myU; move/andP in myU.
            move:(IHmys (proj2 myU) _ IH).
            have K : \sum_(i <- undup mys | i \in undup mys)
            (fm i - (if i == a then fm a else 0)) *: elem i
             = \sum_(i <- undup mys) fm i *: elem i.
             rewrite big_seq; apply eq_bigr=>i P.
            case(i == a) as []eqn:E.
              by move/eqP in E; rewrite -E -mem_undup P in E1.
              by rewrite subr0.
            rewrite K=>L; rewrite L.
            case(b == a) as []eqn:E.
              by move/eqP in E; rewrite E/= eq_refl mulr1.
              by rewrite subr0/= E mulr0 subr0.
        Qed.

      Definition basis : lmodBasisType _
        := lmodBasis.Build li_ span_.
		
	  Definition freeModType := freeLmodPack basis.
    End FreeLmod.

  End Def.
  Module Exports.
    Canonical lc_lmodType.
    Canonical freeModType.
    Notation formalLCType := lc_lmodType.
  End Exports.
End formalLC.
Export formalLC.Exports.

Close Scope ring_scope.
Close Scope lmod_scope.