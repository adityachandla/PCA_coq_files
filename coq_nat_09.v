(* Exercise coq_nat_09 *)

(* Now, let us prove that multiplication is commutative *)

(* For this we may need to use some properties of addition and multiplication  
   that we proved before. *)
Require Import Arith.
Check mult_0_r.
Check plus_comm.
Check plus_assoc.

(* ... and a following auxiliary lemma *)

Lemma mult_succ : forall m n, n + n * m = n * S m.
Proof.
intros.
induction n.
simpl; reflexivity.
simpl.
rewrite <- IHn.
rewrite Nat.add_comm.
rewrite Nat.add_assoc.
rewrite Nat.add_comm with (n := m+n*m).
rewrite Nat.add_assoc.
rewrite Nat.add_comm with (n := n).
reflexivity.
Qed.

Lemma mult_comm : forall m n, m * n = n * m.

Proof.
intros.
induction m.
rewrite Nat.mul_0_r.
simpl.
reflexivity.
simpl.
rewrite IHm.
rewrite mult_succ.
reflexivity.
Qed.
