Set Implicit Arguments.
Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Bool.

Notation " ! b " := (negb b) (at level 0).
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(*zadatak 1a*)

Goal forall x y : bool, (x && !y) || (!x && !y) || (!x && y) = !x || !y.
Proof.
destruct x,y; reflexivity.
Qed.

(*zadatak 1b*)

Goal forall x y z : bool, (!(!x && y && z)) && (!(x && y && !z)) && (x && !y && z) = x && !y && z.
Proof.
destruct x, y, z; reflexivity.
Qed.
