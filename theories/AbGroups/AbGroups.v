(******************************************************************************)
(**)
(******************************************************************************)
(* zmodZeroType R == an zmodType structure for the unit type                  *)


Require Import Coq.Program.Tactics.
From mathcomp Require Import ssreflect ssrfun eqtype choice.

Set Warnings "-parsing". (* Some weird bug in ssrbool throws out parsing warnings*)
  From mathcomp Require Import ssrbool.
Set Warnings "parsing".

Set Warnings "-ambiguous-paths". (* Some weird bug in ssralg throws out coercion warnings*)
    From mathcomp Require Import ssralg.
Set Warnings "ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.
Open Scope ring_scope.

Declare Scope zmod_scope.

Module zmodZero.
  Section Def.
  Definition zeroAdd := fun _ _ : unit => tt.
  Definition zeroNeg := fun _ : unit => tt.
  Definition zeroAbGroupA : associative zeroAdd. Proof. by []. Qed.
  Definition zeroAbGroupC : commutative zeroAdd. Proof. by []. Qed.
  Definition zeroAbGroup0z : left_id tt zeroAdd. Proof. by case. Qed.
  Definition zeroAbGroupIz : left_inverse tt zeroNeg zeroAdd. Proof. by case. Qed.

  Definition type : zmodType :=
    ZmodType unit (GRing.Zmodule.Mixin zeroAbGroupA zeroAbGroupC zeroAbGroup0z zeroAbGroupIz).
  End Def.
End zmodZero.

Notation zmodZeroType := zmodZero.type.
Canonical zmodZeroType.

Close Scope zmod_scope.
Close Scope ring_scope.
