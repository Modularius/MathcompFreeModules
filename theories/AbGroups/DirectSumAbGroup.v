(******************************************************************************)
(**)
(******************************************************************************)
(*         M1 \oplus M2 == the zmodType given by pair_lmodType in ssralg.v    *)
(*                         This is an implementation of the direct sum of two *)
(*                         zmodTypes.                        *)
(* \bigoplus_(f in L) I == the lmodType built up iteratively, where L : seq S *)
(*                         for S : eqType and I : S -> lmodType R             *)
(*                         \bigoplus_(f in nil) I is zmodNullType whilst      *)
(*                         \bigoplus_(f in a::L) I is                         *)
(*                               (I a) \oplus (\bigoplus_(f in L) I)          *)
(*                         This is an implementation of the direct sum of an  *)
(*                         arbitrary number of zmodTypes. Note that L is not  *)
(*                         a list of zmodTypes but of some eqType S, which    *)
(*                         are 'converted' to zmodTypes by                    *)
(*                           I : S -> zmodType.                               *)
(*  \bigoplus_(f : F) I == the zmodType equal to \bigoplus_(f in (enum F)) I  *)
(*        \bigoplus_F I == equivalent to \bigoplus_(f : F) I                  *)
(*          \bigoplus I == equivalent to \bigoplus_(f : F) I                  *)
(*                         where I : F -> zmodType                            *)
(******************************************************************************)
(* The following constructions and lemmas relate to M \oplus N,               *)
(* the direct sum of the pair of zmodTypes M and N                            *)
(******************************************************************************)
(*  \proj1^(M,N)   == the additive projection from M \oplus N to M            *)
(*  \proj2^(M,N)   == the additive projection from M \oplus N to N            *)
(*  \incl1^(M,N)   == the additive inclusion from M to M \oplus N             *)
(*  \incl2^(M,N)   == the additive inclusion from N to M \oplus N             *)
(*  incl1_injective  == a proof that \incl1^(M,N) is injective                *)
(*  incl2_injective  == a proof that \incl2^(M,N) is injective                *)
(*  proj1_incl1K     == a proof of \proj1^(M,N) (\incl1^(M,N) x) = x          *)
(*  proj2_incl2K     == a proof of \proj2^(M,N) (\incl2^(M,N) x) = x          *)
(*  proj1_incl20     == a proof of \proj1^(M,N) (\incl2^(M,N) x) = 0          *)
(*  proj2_incl10     == a proof of \proj2^(M,N) (\incl1^(M,N) x) = 0          *)
(*  incl_proj12_sum  == a proof that any x : M \oplus N can be written        *)
(*                         x = \incl1^(M,N) (\proj1^(M,N) x)                  *)
(*                              + \incl2^(M,N) (\proj2^(M,N) x)               *)
(*  incl_proj12_idem == a proof that rewriting with incl_proj12_sum is        *)
(*                         idempotent                                         *)
(******************************************************************************)
(* Let M N M1 M2 N1 N2 : zmodType                                             *)
(* We define construction for combining linear maps so to be compatible       *)
(* with direct sums                                                           *)
(******************************************************************************)
(* Let f1 : {additive M1 -> N1} and f2 : {additive M2 -> N2}                  *)
(* \diagmap(f,g) == the additive map : M1 \oplus M2 -> N1 \oplus N2           *)
(*                         given by \diagmap(f,g) (x,y) = (f x, g y)          *)
(******************************************************************************)
(* Let f1 : {additive M1 -> N} and f2 : {additive M2 -> N}                    *)
(* \rowmap(f,g) == the additive map : M1 \oplus M2 -> N                       *)
(*                         given by \rowmap(f,g) (x,y) = f x + g y            *)
(******************************************************************************)
(* Let f1 : {additive M -> N1} and f2 : {additive M -> N2}                    *)
(* \colmap(f,g) == the additive map : M -> N1 \oplus N2                       *)
(*                         given by \colmap(f,g) x = (f x, g x)               *)
(******************************************************************************)
(* The following constructions and lemmas relate to \bigoplus_(f : F) I,      *)
(* the direct sum of the zmodTypes given by (I : F -> zmodType), and F is a   *)
(* finite index set (i.e. a finType)                                          *)
(******************************************************************************)
(*  \proj_f^(I)    == the additive projection from \bigoplus I to (I f),      *)
(*                 for f : F. This function is surjective                     *)
(*  \incl_f^(I)    == the additive inclusion from (I f) to \bigoplus I,       *)
(*                 for f : F. This function is injective                      *)
(*  incl_injective == a proof that \incl_f^(I) is injective for f : F         *)
(*  proj_inclK     == a proof that \incl_f^(I) and \proj_f^(I) cancel         *)
(*  proj_incl0     == a proof that \incl_f^(I) and \proj_(f')^(I) equals zero *)
(*                    if f != f'                                              *)
(*  incl_proj_sum  == rewrites element x : \bigoplus I as                     *)
(*                        \sum_(f : F)\incl_f^(I) (\proj_f^(I) x)             *)
(*  incl_proj_idem       ==  a proof that rewriting with incl_proj_sum is     *)
(*                         idempotent                                         *)
(******************************************************************************)
(* The following constructions are used to split and unsplit the direct sum   *)
(* of two direct sums, that is (\bigoplus J) \oplus (\bigoplus K).            *)
(* Doing this involves:                                                       *)
(*  1) three index sets F, G and H,                                           *)
(*  2) a function GH_F : G + H -> F, connecting the sum of G and H to F       *)
(*  3) a proof enumB : enum F = map F_GH (enum sum_finType G H) which         *)
(* establishes that GH_F is an 'isomorphism' of G + H and F as finTypes,      *)
(* and the notations J = I \o GH_F \o inl and K = I \o GH_F \o inr.           *)
(******************************************************************************)
(*     split == a additive function from \bigoplus I to                       *)
(*                    (\bigoplus J) \oplus (\bigoplus K)                      *)
(*   unsplit == a additive function from (\bigoplus J) \oplus (\bigoplus K)   *)
(*                    to \bigoplus I                                          *)
(*  splitK   == a proof that split and unsplit cancel                         *)
(*  unsplitK == a proof that unsplit and split cancel                         *)
(******************************************************************************)
(* DirectSum_UniversalProperty == *)
(******************************************************************************)

From Coq.Init Require Import Notations Datatypes.
Require Import Coq.Program.Tactics.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun seq.
From mathcomp Require Import eqtype fintype bigop.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool ssrnat.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Require Import AbGroups Additives.
Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Include GRing.

Open Scope  zmod_scope.

Section Helpers.
  Variable (S : finType) (X : zmodType) (f : S*S -> X).
  Lemma big_pair_diag_eq :
    \sum_(i : S*S | i.2 == i.1)f i
      = \sum_(i : S) f (i, i).
  Proof.
    have : forall (i : S) (_ : true), f (i, i) = \sum_(j : S) if (j == i) then f (i, j) else 0
    by move=>i _;
    rewrite -big_mkcond (big_pred1 i).
    move=> H; rewrite (eq_bigr _ H); clear H.
    by rewrite pair_bigA -big_mkcond
    (eq_bigr (fun i => f (i.1,i.2)) _)=>/=;
      [|move=>i _; destruct i=>/=].
  Qed.
End Helpers.


Reserved Notation "\bigoplus_ i F"
(at level 36, F at level 36, i at level 50,
  right associativity,
        format "'[' \bigoplus_ i '/ ' F ']'").

Reserved Notation "\bigoplus F"
(at level 36, F at level 36,
  right associativity,
        format "'[' \bigoplus F ']'").

Reserved Notation "\bigoplus_ ( i : t ) F"
(at level 36, F at level 36, i at level 50,
        format "'[' \bigoplus_ ( i : t ) '/ ' F ']'").

Reserved Notation "\bigoplus_ ( i < n ) F"
(at level 36, F at level 36, i, n at level 50,
        format "'[' \bigoplus_ ( i < n ) F ']'").

Reserved Notation "\bigoplus_ ( i 'in' A ) F"
(at level 36, F at level 36, i, A at level 50,
        format "'[' \bigoplus_ ( i 'in' A ) '/ ' F ']'").

Reserved Notation "\proj^( I )_ f "
(at level 36, f at level 36, I at level 36,
  format "'[' \proj^( I )_ f ']'").

Reserved Notation "\inj^( I )_ f "
(at level 36, f at level 36, I at level 36,
  format "'[' \inj^( I )_ f ']'").

Reserved Notation "\proj_ f ^( I ) "
(at level 36, f at level 36, I at level 36,
  format "'[' \proj_ f '^(' I ) ']'").

Reserved Notation "\inj_ f ^( I )"
(at level 36, f at level 36, I at level 36,
  format "'[' \inj_ f '^(' I ) ']'").


Module dsZmod.
  Module Pair.
    Section Def.
      Variable (m1 m2 : zmodType).

      Section Injection.
        Definition inj1_raw := fun x : m1 => (x,zero m2) : pair_zmodType m1 m2.
        Definition inj2_raw := fun x : m2 => (zero m1, x) : pair_zmodType m1 m2.

        Lemma inj1_add : additive inj1_raw.
        Proof. rewrite /inj1_raw/==>x y.
          by symmetry; rewrite /(add _)/=/add_pair/=subr0. Qed.
        Lemma inj2_add : additive inj2_raw.
        Proof. rewrite /inj2_raw/==>x y.
          by symmetry; rewrite /(add _)/=/add_pair/=subr0. Qed.

        Lemma inj1_injective : injective inj1_raw.
        Proof. by move=>x y H; inversion H. Qed.
        Lemma inj2_injective : injective inj2_raw.
        Proof. by move=>x y H; inversion H. Qed.

        Definition inj1 := Additive inj1_add.
        Definition inj2 := Additive inj2_add.

        Lemma inj1_unraw x : inj1_raw x = inj1 x. Proof. by []. Qed.
        Lemma inj2_unraw x : inj2_raw x = inj2 x. Proof. by []. Qed.
      End Injection.

      Section Projection.
        Definition proj1_raw := fun x : pair_zmodType m1 m2 => x.1.
        Definition proj2_raw := fun x : pair_zmodType m1 m2 => x.2.

        Lemma proj1_add : additive proj1_raw.
        Proof. rewrite /proj1_raw/==>x y; destruct x as [x1 x2], y as [y1 y2].
          by rewrite /(add _)/=/add_pair. Qed.
        Lemma proj2_add : additive proj2_raw.
        Proof. rewrite /proj1_raw/==>x y; destruct x as [x1 x2], y as [y1 y2].
          by rewrite /(add _)/=/add_pair. Qed.

        Definition proj1 := Additive proj1_add.
        Definition proj2 := Additive proj2_add.

        Lemma proj1_unraw x : proj1_raw x = proj1 x. Proof. by []. Qed.
        Lemma proj2_unraw x : proj2_raw x = proj2 x. Proof. by []. Qed.

        Lemma proj1_inj1K x : proj1 (inj1 x) = x. Proof. by []. Qed.
        Lemma proj2_inj2K x : proj2 (inj2 x) = x. Proof. by []. Qed.
        Lemma proj1_inj20 x : proj1 (inj2 x) = 0. Proof. by []. Qed.
        Lemma proj2_inj10 x : proj2 (inj1 x) = 0. Proof. by []. Qed.
      End Projection.

      Lemma inj_proj_sum x : x = inj1 (proj1 x) + inj2 (proj2 x).
      Proof.
        rewrite /inj1/proj1/inj2/proj2/(add _)/=
         /add_pair addr0 add0r;
        by destruct x.
      Qed.
    End Def.


    Section Morphisms.
      Section MorphismsToDS.
        Variable (M N1 N2 : zmodType)
          (f1 : {additive M -> N1}) (f2 : {additive M -> N2}).

        Definition to_ds_raw : M -> (pair_zmodType N1 N2)
          := fun x => (inj1 _ _ (f1 x)) + (inj2  _ _ (f2 x)).

        Lemma to_ds_add : additive to_ds_raw.
        Proof. rewrite/to_ds_raw=>x y.
        by rewrite !raddfD !raddfN addrACA. Qed.
        Definition to_ds : {additive M -> (pair_zmodType N1 N2)}
          := Additive to_ds_add.

      End MorphismsToDS.

      Section MorphismsFromDS.
        Variable (M1 M2 N : zmodType)
          (f1 : {additive M1 -> N}) (f2 : {additive M2 -> N}).

        Definition from_ds_raw : (pair_zmodType M1 M2) -> N
          := fun x => (f1 (proj1 _ _ x)) + (f2 (proj2  _ _ x)).

        Lemma from_ds_add : additive from_ds_raw.
        Proof. rewrite/from_ds_raw=>x y.
        by rewrite !raddfD !raddfN addrACA. Qed.

        Definition from_ds : {additive (pair_zmodType M1 M2) -> N}
          := Additive from_ds_add.

      End MorphismsFromDS.

      Section MorphismsDiag.
        Variable (M1 M2 N1 N2 : zmodType)
          (f1 : {additive M1 -> N1}) (f2 : {additive M2 -> N2}).

        Definition diag_raw : (pair_zmodType M1 M2) -> (pair_zmodType N1 N2)
          := fun x => (inj1 _ _ (f1 (proj1 _ _ x))) + (inj2 _ _ (f2 (proj2  _ _ x))).

        Lemma diag_add : additive diag_raw.
        Proof. rewrite/diag_raw=>x y.
        by rewrite !raddfD !raddfN addrACA. Qed.

        Definition diag : {additive (pair_zmodType M1 M2) -> (pair_zmodType N1 N2)}
          := Additive diag_add.

      End MorphismsDiag.

      Section MorphismsDiagCompositions.
        Variable (M1 M2 N1 N2 O1 O2 : zmodType)
          (f1 : {additive M1 -> N1}) (f2 : {additive M2 -> N2})
          (g1 : {additive N1 -> O1}) (g2 : {additive N2 -> O2}).

        Lemma diag_id : diag (\id_M1) (\id_M2) = \id_(pair_zmodType M1 M2).
        Proof.
          rewrite additive_eq.
          apply functional_extensionality=>x/=.
          by rewrite /diag_raw /addID.map -!(lock) -(inj_proj_sum x).
        Qed.

        Lemma diag_comp : (diag g1 g2) \oAdd (diag f1 f2) = diag (g1 \oAdd f1) (g2 \oAdd f2).
        Proof.
          rewrite additive_eq.
          apply functional_extensionality=>x.
          rewrite -!addCompChain=>/=.
          rewrite /diag_raw -!addCompChain=>/=.
          by rewrite addr0 add0r.
        Qed.

      End MorphismsDiagCompositions.
    End Morphisms.

    Module Exports.
      Notation zmodDSPairType := pair_zmodType.
      Infix "\oplus" := (pair_zmodType) (at level 35) : zmod_scope.
      Notation "\diagmap( f , g )" := (diag f g) (at level 35) : zmod_scope.
      Notation "\rowmap( f , g )" := (from_ds f g) (at level 35) : zmod_scope.
      Notation "\colmap( f , g )" := (to_ds f g) (at level 35) : zmod_scope.
    End Exports.
  End Pair.
  Export Pair.Exports.



  Module Seq.
    Section Ring.
      Section Environment.
        Variable (T : eqType) (I : T -> zmodType).

        Section Def.
          Definition Nth := (fun L n => match (seq.nth None (map Some L) n) with
          |Some t => I t
          |None => zmodZeroType
          end).

          Fixpoint DS (L : seq T) : zmodType := match L with
            |nil => zmodZeroType
            |a'::L' => (I a') \oplus (DS L')
          end.
        End Def.

        Section Injection.
        Fixpoint inj_raw (L : seq T) (n : nat) {struct n} :
          Nth L n -> DS L
        := match L as LL return Nth LL n -> DS LL with
          |nil => fun _ => tt
          |a::L' => match n as nn return Nth (a::L') nn -> DS (a::L') with
            |0    => fun x => @Pair.inj1 (I a) (DS L') x
            |S n' => fun x => @Pair.inj2 (I a) (DS L') ((@inj_raw L' n') x)
            end
          end.

          Lemma inj_add (L : seq T) (n : nat) : additive (@inj_raw L n).
          Proof. move: n; induction L.
            induction n=>//.
            move : L IHL; induction n=>// x y.
            apply (@Pair.inj1_add (I a) (DS L)).
            by rewrite /=-(@Pair.inj2_add (I a) (DS L)) (IHL n).
          Qed.

          Lemma inj_injective
            (L : seq T) (n : nat) : injective (@inj_raw L n).
          Proof. move: n; induction L=>//=.
          { induction n; by move=> x y; destruct x, y. }
            move: L IHL.
            induction n=>/= x y H.
            apply (@Pair.inj1_injective _ _ x y H).
            apply (IHL n x y (@Pair.inj2_injective _ _ (@inj_raw L n x) (@inj_raw L n y) H)).
          Qed.
        End Injection.
        Definition inj (L : seq T) (n : nat)
          := Additive (@inj_add L n).

        Section Projection.
          Fixpoint proj_raw (L : seq T) (n : nat) {struct n} :
          DS L -> Nth L n
        := match L as LL return DS LL -> Nth LL n with
          |nil => match n as nn return zmodZero.type -> Nth nil nn with
            |0    => fun _ => tt
            |S n' => fun _ => tt
            end
          |a::L' => match n as nn return DS (a::L') -> Nth (a::L') nn with
            |0    => fun x => @Pair.proj1 (I a) (DS L') x
            |S n' => fun x => (@proj_raw L' n') (@Pair.proj2 (I a) (DS L') x)
            end
          end.
          
          Lemma proj_add (L : seq T) (n : nat) : additive (@proj_raw L n).
          Proof. move: n; induction L=>//=. induction n=>//.
            move: L IHL; induction n=>//=; move=> x y.
            by rewrite !Pair.proj2_unraw raddfD -(IHL n).
          Qed.
        End Projection.
        Definition proj (L : seq T) (n : nat)
          := Additive (@proj_add L n).

        Section Results.
          Section Lemmas.
            Variable (L : seq T).    
            Lemma nth_cons {a d} {n : nat} : seq.nth d (a::L) (S n) = seq.nth d L n.
            Proof. by induction n. Qed.
        
            Lemma inj_cons n a x : @inj (a::L) (S n) x = Pair.inj2 (I a) _ (@inj L n x).
            Proof. by []. Qed.
        
            Lemma proj_cons n a x : @proj (a::L) (S n) (Pair.inj2 (I a) _ x) = @proj L n x.
            Proof. by []. Qed.

            Lemma proj_inj_cons (n n' : nat) a x
            : @proj (a::L) (n.+1) (@inj (a::L) (n'.+1) x) = @proj L n (@inj L n' x).
            Proof. by []. Qed.
          End Lemmas.
          Variable (L : seq T).

          (* The following two lemmas are used for cancellation *)
          Lemma proj_injK_ofsize (n : 'I_(size L)) x : @proj L (nat_of_ord n) (@inj L (nat_of_ord n) x) = x.
          Proof.
            induction L=>//; destruct n as [n N]=>//.
            induction n=>//; move:x; simpl (Ordinal N : nat)=>x.
            rewrite -ltn_predRL in N.
            by rewrite proj_inj_cons (IHl (Ordinal N)).
          Qed.

          Lemma proj_inj0_ofsize (n n' : 'I_(size L)) x : (nat_of_ord n) != n' -> @proj L n (@inj L n' x) = 0.
          Proof.
            induction L; destruct n as [n N], n' as [n' N']=>//.
            simpl in x, IHl, N, N'=>H.
            induction n.
              apply (rwP negP) in H.
              by induction n'=>/=; [contradiction H|].
            induction n'=>//=.
              by (have: proj l n 0 = 0 by rewrite raddf0).
            clear IHn' IHn;
            rewrite eqSS in H;
            rewrite ltnS in N;
            rewrite ltnS in N';
            by apply (IHl (Ordinal N) (Ordinal N') x H).
          Qed.
          
          (* The following two lemmas are the same as above but more versitile,
          in that they don't require the index to be an ordinal of size L, simply
          that they are naturals less than size L *)
          Lemma proj_injK (n : nat) x (M : n < size L) : @proj L n (@inj L n x) = x.
          Proof. apply (@proj_injK_ofsize (Ordinal M)). Qed.
      
          Lemma proj_inj0 m1 m2 (n : 'I_m1) (n' : 'I_m2) x (M1 : m1 <= (size L)) (M2 : m2 <= (size L))
            : (nat_of_ord n) != n' -> @proj L n (@inj L n' x) = 0.
          Proof. apply (@proj_inj0_ofsize (widen_ord M1 n) (widen_ord M2 n')). Qed.

          (* this lemma expresses any element as a sum of projections *)
          Lemma inj_proj_sum x : x = \sum_(n < size L) inj L (nat_of_ord n) (@proj L (nat_of_ord n) x).
          Proof.
            induction L.
            by rewrite /size big_ord0; case x.
            destruct x as [Ia DSl].
            by rewrite big_ord_recl {1}(IHl DSl)
            (Pair.inj_proj_sum (Ia, _)) raddf_sum.
          Qed.
        End Results.

        (* Given a direct sum indexed by a seq, we define a function to reform
        the direct sum into the direct sum of two smaller direct sums. *)
        Section Operations.
          Variable (L1 L2 : seq T).
          (*Tr = truncate, Ap = Append, R = right, L = left*)
          Section L1.
            Variable (n : 'I_(size L1)).
            Lemma catTrR_eq : (Nth (L1 ++ L2) n) = (Nth L1 n).
            Proof. destruct n as [n' H].
            by rewrite/Nth map_cat nth_cat size_map H. Qed.

            Definition catTrR : (Nth (L1 ++ L2) n) -> (Nth L1 n).
            Proof. by rewrite catTrR_eq. Defined.

            Definition catApR : (Nth L1 n) -> (Nth (L1 ++ L2) n).
            Proof. by rewrite catTrR_eq. Defined.

            Lemma catTrApR_add : additive catTrR /\ additive catApR.
            Proof. split; rewrite/catTrR/catApR=>x y; by destruct(catTrR_eq). Qed.

            Lemma catApTrRK : cancel catTrR catApR /\ cancel catApR catTrR.
            Proof. split; rewrite/catApR/catTrR=>x; by destruct(catTrR_eq). Qed.

            Definition catifyL1 : addIsomType (Nth (L1 ++ L2) n) (Nth L1 n)
            := addIsomBuildPack catTrApR_add catApTrRK.
          End L1.
          Section L2.
            Variable (n : 'I_(size L2)).
        
            Lemma catTrL_eq : (Nth (L1 ++ L2) (rshift (size L1) n)) = (Nth L2 n).
            Proof. by simpl; rewrite/Nth map_cat nth_cat size_map
            -{2}(addn0 (size L1)) ltn_add2l addnC addnK. Qed.

            Definition catTrL : (Nth (L1 ++ L2) (rshift (size L1) n)) -> (Nth L2 n).
            Proof.  by rewrite catTrL_eq. Defined.

            Definition catApL : (Nth L2 n) -> (Nth (L1 ++ L2) (rshift (size L1) n)).
            Proof. by rewrite catTrL_eq. Defined.

            Lemma catTrApL_add : additive catTrL /\ additive catApL.
            Proof. split; rewrite/catTrL/catApL=>x y;by destruct (catTrL_eq). Qed.
            
            Lemma catApTrLK : cancel catTrL catApL /\ cancel catApL catTrL.
            Proof. split; rewrite/catApL/catTrL=>x; by destruct(catTrL_eq). Qed.

            Definition catifyL2 : addIsomType (Nth (L1 ++ L2) (rshift (size L1) n)) (Nth L2 n)
            := addIsomBuildPack catTrApL_add catApTrLK.
          End L2.

          Definition split_raw : DS (L1 ++ L2) -> DS L1 \oplus DS L2
            := fun x =>
            (\sum_(n < size L1)(inj L1 n \oAdd catifyL1 n \oAdd proj (L1 ++ L2) n ) x,
            \sum_(n < size L2)(inj L2 n \oAdd catifyL2 n \oAdd proj (L1 ++ L2) (rshift (size L1) n)) x).

          Definition unsplit_raw : DS L1 \oplus DS L2 -> DS (L1 ++ L2)
          := fun x =>
            \sum_(n < size L1)((inj (L1 ++ L2) n                     \oAdd inv(catifyL1 n) \oAdd proj L1 n) x.1) +
            \sum_(n < size L2)((inj (L1 ++ L2) (rshift (size L1) n)  \oAdd inv(catifyL2 n) \oAdd proj L2 n) x.2).

          Lemma split_add : additive split_raw.
          Proof. rewrite/split_raw=>x y/=.
            by rewrite (rwP eqP)/eq_op -(rwP andP) -!(rwP eqP)/=
             -!sumrB !(eq_bigr _ (fun i _ => raddfB _ _ _)).
          Qed.

          Lemma unsplit_add : additive unsplit_raw.
          Proof. rewrite/unsplit_raw=>x y/=.
            rewrite !(eq_bigr _ (fun i _ => raddfB _ _ _)) !sumrB/=.
            Admitted.

          Definition split := Additive split_add.
          Definition unsplit := Additive unsplit_add.

          Lemma unsplitK : cancel split unsplit.
          Proof. simpl; rewrite /unsplit_raw/split_raw=>x.
            under eq_bigr do rewrite raddf_sum.
            under eq_bigr do under eq_bigr do rewrite -!addCompChain.
            under[\sum_(_ < size L2) _] eq_bigr do rewrite raddf_sum.
            under[\sum_(_ < size L2) _] eq_bigr do under eq_bigr do rewrite -!addCompChain.
            rewrite!pair_bigA.
            rewrite (eq_bigr (fun p : 'I_(size L1)*'I_(size L1)
            => if p.2 == p.1
              then inj _ p.1 (proj _ p.1 x)
              else 0 ) _).
            rewrite (eq_bigr (fun p : 'I_(size L2)*'I_(size L2)
              => if p.2 == p.1
              then inj _ (rshift (size L1) p.2) (proj _ (rshift (size L1) p.2) x)
              else 0 ) _).
            by rewrite -!big_mkcond !big_pair_diag_eq {3}(@inj_proj_sum _ x)
            size_cat (@big_split_ord _ _ _ (size L1) (size L2)).
            by move=>p _; case (p.2 == p.1) as []eqn:E;
            [apply (rwP eqP) in E; rewrite E proj_injK_ofsize (isomaK (catifyL2 p.1)) |
            rewrite proj_inj0_ofsize; [rewrite !raddf0|
              rewrite eq_sym/eq_op in E; simpl in E; rewrite E]].
            by move=>p _; case (p.2 == p.1) as []eqn:E;
            [ apply (rwP eqP) in E; rewrite E proj_injK_ofsize (isomaK (catifyL1 p.1))|
            rewrite proj_inj0_ofsize; [rewrite !raddf0|
              rewrite eq_sym/eq_op in E; simpl in E; rewrite E]].
          Qed.

          Lemma splitK : cancel unsplit split.
          Proof. simpl; rewrite /unsplit_raw/split_raw=>x.
          under eq_bigr do rewrite !raddfD.
          under[\sum_(n < _) ((_ \oAdd _ \oAdd proj _ (rshift _ n)) _)]
            eq_bigr do rewrite !raddfD.

          rewrite !big_split !(eq_bigr _ (fun i _ => raddf_sum _ _ _ _)) !pair_bigA.
          rewrite (eq_bigr (fun p : 'I_(size L1)*'I_(size L1)
          => if(p.2 == p.1)
            then inj L1 p.1 (proj L1 p.1 x.1)
            else 0) _).
          rewrite (eq_bigr (fun p : 'I_(size L2)*'I_(size L2)
          => if(p.2 == p.1)
            then inj L2 p.2 (proj L2 p.2 x.2)
            else 0) _).
          {
            destruct x as [x1 x2];
            rewrite -!big_mkcond !big_pair_diag_eq
            (eq_bigr (fun p : 'I_(size L1) => inj _ p (proj _ p x1)) _);[|by move].
            rewrite (eq_bigr (fun p : 'I_(size L2) => inj _ p (proj _ p x2)) _); [| by []].
            rewrite {4}(inj_proj_sum x1) {4}(inj_proj_sum x2) (rwP eqP) /eq_op -(rwP andP).
            split; rewrite -subr_eq0.

            rewrite {1}addrC addrA addNr add0r (eq_bigr (fun _ => 0) _).
            rewrite big_const cardE /iter enumT;
            induction(Finite.enum _)=>//=; by rewrite add0r.

            move =>[[p1 H1] [p2 H2]] _;
            rewrite -!addCompChain proj_inj0;[by rewrite !raddf0 |by rewrite size_cat leq_addr|by rewrite size_cat|];
            rewrite -(rwP negP)/not -(rwP eqP)=>/=N;
            by rewrite N -{2}(addn0 (size L1)) ltn_add2l in H1.

            rewrite -addrA addrN addr0 (eq_bigr (fun _ => 0) _).
            rewrite big_const cardE /iter enumT;
            induction(Finite.enum _)=>//=; by rewrite add0r.

            move =>[[p1 H1] [p2 H2]] _;
            rewrite -!addCompChain proj_inj0;[by rewrite !raddf0 |by rewrite size_cat|by rewrite size_cat leq_addr|];
            rewrite -(rwP negP)/not -(rwP eqP)=>/=N.
            by rewrite -N -{2}(addn0 (size L1)) ltn_add2l in H2.
          }
          move=>p _; case(p.2 == p.1) as []eqn:E.
          move/eqP in E; rewrite E -!addCompChain.
          rewrite proj_injK; [by rewrite isomKa|].
          destruct p as [[p1 H1] [p2 H2]].
          by rewrite size_cat ltn_add2l.
          rewrite -!addCompChain proj_inj0; [by rewrite !raddf0|by rewrite size_cat|by rewrite size_cat|].
          rewrite /eq_op in E; simpl in E.
          by rewrite /rshift eqn_add2l eq_sym E.

          move=>p _; case(p.2 == p.1) as []eqn:E.
          apply (rwP eqP) in E; rewrite -E -!addCompChain.
          rewrite proj_injK; [by rewrite isomKa|].
          destruct p as [[p1 H1] [p2 H2]]=>/=.
          by rewrite size_cat addnC (ltn_addl _ H2).
          rewrite -!addCompChain proj_inj0; [by rewrite !raddf0|by rewrite size_cat leq_addr|by rewrite size_cat leq_addr|].
          rewrite /eq_op in E; simpl in E.
          by rewrite eq_sym E.
          Qed.
        End Operations.
      End Environment.
      
      Section Hom.
        Variable (S T : eqType) (I : T -> zmodType) (T_S : S -> T).

        Fixpoint homify_raw (L : seq S) : DS (I \o T_S) L -> DS I (map T_S L)
          := match L with
          |nil => id
          |a::l => fun x => (x.1 , homify_raw x.2)
          end.
        Fixpoint unhomify_raw (L : seq S) : DS I (map T_S L) -> DS (I \o T_S) L
          := match L with
          |nil => id
          |a::l => fun x => (x.1 , unhomify_raw x.2)
          end.
        
        Variable (L : seq S).
        Lemma homify_add : additive (@homify_raw L) /\ additive (@unhomify_raw L).
        Proof. split; induction L=>//=x y;
          by rewrite IHl/homify_raw/unhomify_raw.
        Qed.
        Lemma homifyK : cancel (@homify_raw L) (@unhomify_raw L) /\ cancel (@unhomify_raw L) (@homify_raw L).
        Proof. split; induction L=>//=x; destruct x;
          by rewrite IHl.
        Qed.
        Definition homify := addIsomBuildPack homify_add homifyK.
      End Hom.

      Section Bijection.
        Variable (S T : eqType) (I : T -> zmodType)
            (T_S : S -> T) (S_T : T -> S) (Inj : cancel S_T T_S).

        Variable (L : seq T).
        Definition mapify_raw : DS I (map T_S (map S_T L)) -> DS I L.
        by rewrite mapK. Defined.
        Definition unmapify_raw : DS I L -> DS I (map T_S (map S_T L)).
        by rewrite mapK. Defined.
        Lemma mapify_add : additive mapify_raw /\ additive unmapify_raw.
        Proof. split; by rewrite/mapify_raw/unmapify_raw; destruct mapK. Qed.
        Lemma mapifyK : cancel mapify_raw unmapify_raw /\ cancel unmapify_raw mapify_raw.
        Proof. split; by rewrite/mapify_raw/unmapify_raw; destruct mapK. Qed.
        Definition mapify := addIsomBuildPack mapify_add mapifyK.

        Definition bijectify := addIsomConcat (homify I T_S (map S_T L)) mapify.
      End Bijection.
    End Ring.
  End Seq.









  Section General.
    Section Def.
      Variable (F : finType) (I : F -> zmodType).

      Definition DS : zmodType := Seq.DS I (enum F).

      Section Components.
        Variable (f : F).

        Lemma cardElt : nat_of_ord (enum_rank f) < size (enum F).
        Proof. rewrite -cardE; apply ltn_ord. Qed.

        Definition Ord := Ordinal cardElt.
        Definition Nth := Seq.Nth I (enum F) Ord.

        Section TypeConversion.
          Lemma Nth_If_eq : Nth = I f.
          Proof. by rewrite /Nth/Seq.Nth -codomE nth_codom enum_rankK. Qed.
          Lemma If_Nth_eq : I f = Nth.
          Proof. by rewrite Nth_If_eq. Qed.

          Definition finify_raw : Nth -> I f := (fun fn : Nth
            -> Nth => eq_rect_r (fun M : zmodType => Nth -> M)
              fn If_Nth_eq) id.
          Definition unfinify_raw : I f -> Nth := (fun fn : Nth
            -> Nth => eq_rect_r (fun M : zmodType => M -> Nth)
              fn If_Nth_eq) id.
          Lemma finify_add : additive finify_raw /\ additive unfinify_raw.
          Proof. split; by rewrite /finify_raw/unfinify_raw=>x y; destruct If_Nth_eq. Qed.
          Lemma finifyK : cancel finify_raw unfinify_raw /\ cancel unfinify_raw finify_raw.
          Proof. split; by rewrite/finify_raw/unfinify_raw; destruct If_Nth_eq. Qed.

          Definition finify := addIsomBuildPack finify_add finifyK.

        End TypeConversion.

        Section Projection.
          Definition proj_raw : DS -> I f
          := finify \oAdd (@Seq.proj F I (enum F) Ord).

          Lemma proj_add : additive proj_raw.
          Proof. rewrite/proj_raw=> x y; by rewrite !raddfB. Qed.

          Definition proj : {additive DS -> I f} := Additive proj_add.
        End Projection.

        Section Injection.
          Definition inj_raw : I f -> DS
          := (@Seq.inj F I (enum F) Ord) \oAdd inv(finify).

          Lemma inj_add : additive inj_raw.
          Proof. rewrite/inj_raw=> x y; by rewrite !raddfB. Qed.

          Lemma inj_injective : injective inj_raw.
          Proof. rewrite/inj_raw=>x y; rewrite -!addCompChain=>H.
            apply Seq.inj_injective in H.
            apply (congr1 finify) in H.
            by rewrite !isomKa in H.
          Qed.

          Definition inj : {additive I f -> DS} := Additive inj_add.
        End Injection.
      End Components.

      Section Results.
        Lemma proj_injK (f : F) x : proj f (inj f x) = x.
        Proof. by rewrite /proj_raw/inj_raw -!addCompChain
          Seq.proj_injK; [rewrite -{2}(isomKf (finify f) x) | apply cardElt].
        Qed.

        Lemma proj_inj0 (f f' : F) x : f != f' -> @proj f (@inj f' x) = 0.
        Proof.
          rewrite-(rwP negP)/not -!addCompChain=>H.
          case((nat_of_ord (enum_rank f) != enum_rank f')) as []eqn:E.
          rewrite (@Seq.proj_inj0_ofsize _ _ _ (Ord f) (Ord f') _ E).
          by rewrite raddf0.
          assert (E' := contraFeq (fun B : enum_rank f != enum_rank f' => B) E).
          apply enum_rank_inj in E'.
          rewrite E' eq_refl in H.
          by assert (H' := H is_true_true).
        Qed.

        Lemma inj_proj_sum x : x = \sum_(f : F) inj f (proj f x).
        Proof.
          rewrite big_enum_val.
          rewrite {1}(Seq.inj_proj_sum x) -!big_enum  -cardT.
          refine (eq_bigr _ _).
          move=> i _; rewrite /inj_raw/proj_raw/Seq.inj/Seq.proj
          -!addCompChain (isomaK (finify _))/Ord=>/=.
          by rewrite enum_valK.
        Qed.

        Lemma inj_proj_idem x : \sum_(f : F) inj f (proj f (\sum_(f : F) inj f (proj f x))) = \sum_(f : F) inj f (proj f x).
        Proof. by rewrite -inj_proj_sum. Qed.
      End Results.
    End Def.
    Section Hom.
(*      Variable (F G : finType) (I : F -> lmodType R) (J : G -> lmodType R)
      (J = I \o F_G)
      (F_G : G -> F) (enumB : enum F = map F_G (enum G)).

      Definition enumify_raw : Seq.DS I (map F_G (enum G)) -> DS I.
      by rewrite /DS enumB. Defined.
      Definition unenumify_raw : DS I -> Seq.DS I (map F_G (enum G)).
      by rewrite /DS enumB. Defined.
      Lemma enumify_lin : linear enumify_raw /\ linear unenumify_raw.
      Proof. split; rewrite /enumify_raw/unenumify_raw; by destruct enumB. Qed.
      Lemma enumifyK : cancel enumify_raw unenumify_raw /\ cancel unenumify_raw enumify_raw .
      Proof. split; rewrite /enumify_raw/unenumify_raw; by destruct enumB. Qed.
      Definition enumify := linIsomBuildPack enumify_lin enumifyK.

      Definition homify : {linear DS (I \o F_G) -> DS I}
      := enumify \oLin (@Seq.homify _ _ _ I F_G (enum G)).
      Definition unhomify : {linear DS I -> DS (I \o F_G)}
      := inv(@Seq.homify _ _ _ I F_G (enum G)) \oLin inv(enumify).*)
    End Hom.
    Section Bijection.
    (*
      Variable (F G : finType) (I : F -> lmodType R) (J : G -> lmodType R)
        (F_G : G -> F) (G_F : F -> G)
        (I_J : I = J \o G_F) (J_I : J = I \o F_G)
        (Inj : cancel F_G G_F) (Surj : cancel G_F F_G) (enumB : enum F = map F_G (enum G)).


        Definition mapify_raw : DS (I \o S_T \o T_S) -> DS I.
        by rewrite mapK. Defined.      
        Definition unmapify_raw : DS I L -> DS I (map T_S (map S_T L)).
        by rewrite mapK. Defined.
        Lemma mapify_lin : linear mapify_raw /\ linear unmapify_raw.
        Proof. split; by rewrite/mapify_raw/unmapify_raw; destruct mapK. Qed.
        Lemma mapifyK : cancel mapify_raw unmapify_raw /\ cancel unmapify_raw mapify_raw.
        Proof. split; by rewrite/mapify_raw/unmapify_raw; destruct mapK. Qed.
        Definition mapify := linIsomBuildPack mapify_lin mapifyK.

        Definition bijectify := linIsomConcat (homify I T_S (map S_T L)) mapify.*)
    End Bijection.

    Section Operations.
      Variable (F G : finType) (I : F + G -> zmodType).
      Definition J : F -> zmodType := I \o inl.
      Definition K : G -> zmodType := I \o inr.

      Lemma sumify_eq : (enum (sum_finType F G)) = ((map inl (enum F)) ++ (map inr (enum G))).
      Proof. by rewrite/DS enumT(unlock _)/=/sum_enum -!enumT. Qed.

      Definition sumify_raw : DS I -> Seq.DS I ((map inl (enum F)) ++ (map inr (enum G))).
      by rewrite /DS sumify_eq. Defined.
      Definition unsumify_raw : Seq.DS I ((map inl (enum F)) ++ (map inr (enum G))) -> DS I.
      by rewrite /DS sumify_eq. Defined.
      
      Lemma sumify_add : additive sumify_raw /\ additive unsumify_raw.
        Proof. split; rewrite/sumify_raw/unsumify_raw=>x y;
        by destruct sumify_eq. Qed.
      Lemma sumifyK : cancel sumify_raw unsumify_raw /\ cancel unsumify_raw sumify_raw.
        Proof. split; rewrite/sumify_raw/unsumify_raw=>x;
        by destruct sumify_eq. Qed.
	    Definition sumify := addIsomBuildPack sumify_add sumifyK.
      
      Definition split : DS I -> DS J \oplus DS K
       := \diagmap(inv(Seq.homify _ inl _), inv(Seq.homify _ inr _))
			      \oAdd (Seq.split I _ _) \oAdd sumify.

      Definition unsplit : {additive DS J \oplus DS K -> DS I}
      := inv(sumify) \oAdd (Seq.unsplit I _ _) \oAdd
          \diagmap(Seq.homify _ inl _, Seq.homify _ inr _).

      Lemma unsplitK : cancel split unsplit.
      Proof. rewrite /unsplit/split=>x.
        by rewrite -!addCompChain (addCompChain (\diagmap(_,_)) (\diagmap(_,_)))
        Pair.diag_comp !addIsom.concatKa Pair.diag_id -addIDChain
        Seq.unsplitK (isomaK sumify).
      Qed.

      Lemma splitK : cancel unsplit split.
      Proof. rewrite /unsplit/split=>x.
        by rewrite -!addCompChain isomKa Seq.splitK
        (addCompChain (\diagmap(_,_)) (\diagmap(_,_)))
        Pair.diag_comp !addIsom.concataK Pair.diag_id -addIDChain.
      Qed.

    End Operations.

  End General.
  Section Results.
  Variable (M N : zmodType) (m : M) (n : N).
  Lemma pair_eq_seq (F G : eqType) (f : F -> M) (g : G -> N)
    (L1 : seq F) (L2 : seq G) :
    \sum_(i <- L1) (f i, 0)%R + \sum_(i <- L2) (0, g i) == (m,n)
    <-> (\sum_(i <- L1) f i == m /\ \sum_(i <- L2) g i == n).
  Proof. split; [move=> H|move=> [H1 H2]]. {
    have:(\sum_(i <- L1) (dsZmod.Pair.inj1 M N (f i)) + \sum_(i <- L2) (dsZmod.Pair.inj2 M N (g i)) == (m, n))
      by apply H .
    rewrite -!raddf_sum/Pair.inj1/Pair.inj2/(@add _)/=
     /add_pair add0r addr0 -(rwP eqP)=>H0;
    by inversion H0.
  }
  move: H1 H2; rewrite -!(rwP eqP)=>H1 H2.
  have:(\sum_(i <- L1) (Pair.inj1 _ _  (f i)) == (m, @zero N))
    by rewrite -raddf_sum/Pair.inj1 H1.
  have:(\sum_(i <- L2) (Pair.inj2 _ _ (g i)) == (@zero M, n))
    by rewrite -raddf_sum/Pair.inj2 H2=>/=.
  rewrite -!(rwP eqP)=>H H0.
  have:(\sum_(i <- L1) (dsZmod.Pair.inj1 _ _ (f i)) + \sum_(i <- L2) (dsZmod.Pair.inj2 _ _ (g i)) == (m, n))
    by rewrite H H0 {1}/(@add (pair_zmodType M N))/=
    /add_pair add0r addr0.
  by rewrite /Pair.inj1/Pair.inj2 -(rwP eqP).
  Qed.

    Lemma pair_eq (F G : finType) (f : F -> M) (g : G -> N) :
    \sum_i (f i, 0)%R + \sum_i (0, g i) == (m,n)
    <-> (\sum_i f i == m /\ \sum_i g i == n).
  Proof. by rewrite -big_enum/=pair_eq_seq big_enum/=. Qed.
  End Results.
End dsZmod.

Definition dsProj (F : finType) (I : F -> zmodType) (f : F) := @dsZmod.proj F I f.
Definition dsInj (F : finType) (I : F -> zmodType) (f : F) := @dsZmod.inj F I f.




Export dsZmod.Pair.Exports.
Notation "\bigoplus_ i F" := (dsZmod.DS (fun i => F i)) : zmod_scope.
Notation "\bigoplus F" := (dsZmod.DS F) : zmod_scope.
Notation "\bigoplus_ ( i : t ) F" := (dsZmod.DS (fun i : t => F i)) : zmod_scope.
Notation "\bigoplus_ ( i 'in' A ) F" := (dsZmod.Seq.DS (filter F (fun i => i \in A))) : zmod_scope.
Notation "\proj^( I )_ f " := (dsZmod.proj I f ) : zmod_scope.
Notation "\inj^( I )_ f " := (dsZmod.inj I f ) : zmod_scope.
Notation "\proj_ f ^( I )" := (dsZmod.proj I f ) : zmod_scope.
Notation "\inj_ f ^( I )" := (dsZmod.inj I f ) : zmod_scope.

Theorem DirectSum_UniversalProperty (F : finType)
  (I : F -> zmodType)
    : forall (f : forall i : F, {additive \bigoplus I -> (I i)}), 
      exists (g : forall i : F, {additive (I i) -> (I i)}),
        forall i : F, f i \oAdd \inj_i^(I) = g i.
Proof. move=> f.
  by refine(ex_intro _ (fun i => f i \oAdd \inj_i^(I)) _ ).
Qed.

Close Scope  zmod_scope.
Close Scope  ring_scope.