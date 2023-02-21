(* Exercise coq_nat_03 *)

(* Let us prove a simple property concerning addition and successor *)

Lemma plus_succ : forall m n, S (m + n) = m + S n.

Proof.
intros.
induction m.
simpl.
reflexivity.
simpl.
rewrite IHm.
reflexivity.
 
Qed.
