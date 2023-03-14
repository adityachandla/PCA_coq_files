(* Exercise coq_nat_10 *)

(* Multiplication distributes over addition *)

Require Import Arith.

Print Nat.add_assoc.
Print Nat.add_comm.

Lemma mult_plus_distr : forall m n p, m * (n + p) = m * n + m * p.

Proof.
 intros.
 induction m.
 rewrite Nat.mul_0_l.
 reflexivity.
 simpl.
 rewrite IHm.
 rewrite Nat.add_assoc.
 rewrite Nat.add_assoc with (m := p).
 rewrite Nat.add_comm with (n := n+p).
 rewrite Nat.add_assoc.
 rewrite Nat.add_comm with (n := m*n).
 reflexivity.
Qed.
