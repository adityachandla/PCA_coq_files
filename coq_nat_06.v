(* Exercise coq_nat_06 *)

(* Let us prove that addition is associative *)
Require Import Plus.

Check Nat.add_comm.
Print Nat.add_assoc.

Lemma plus_assoc : forall m n p, m + (n + p) = (m + n) + p.

Proof.
intros.
induction m.
simpl.
reflexivity.
simpl.
rewrite IHm.
reflexivity.
Qed.