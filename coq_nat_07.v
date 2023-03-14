(* Exercise coq_nat_07 *)

(* So far we were dealing with addition on natural numbers. How
   about multiplication? Not surprisingly it is defined in the
   standard library of Coq, but before seeing the definition
   try to think of how would you define that (using addition). *)
Print mult.
Check mult.

(* Here is this definition for reference (and in the way you would
   type it in, which slightly differs from the way Coq presents it)
   
Fixpoint mult (n m:nat) {struct n} : nat :=
  match n with
  | O => 0
  | S p => m + mult p m
  end
*)

(* Let us prove the 0 properties of multiplication *)

Lemma mult_0_l : forall n, 0 * n = 0.

Proof.
intros.
unfold mult.
reflexivity.
 
Qed.

Lemma mult_0_r : forall n, n * 0 = 0.

Proof.
intros.
induction n.
simpl; reflexivity.
simpl.
assumption.
Qed.