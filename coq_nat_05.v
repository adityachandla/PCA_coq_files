(* Exercise coq_nat_05 *)

(* In the Exercise coq_nat_2 we proved directly that '0' is 
   right-neutral for addition. Now let us prove the same fact 
   using the facts that it is left-neutral and using commutativity
   of addition.
*)
Require Import Plus.
Check plus_comm.
Check plus_0_l.

Lemma plus_0_r : forall n, n + 0 = n.

Proof.
intros.
elim n.
simpl ; reflexivity.
intros ; simpl ; rewrite H ; reflexivity.

Qed.
