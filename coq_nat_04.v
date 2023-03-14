(* Exercise coq_nat_04 *)

(* Let us prove that addition is commutative. *)

(* For this we may need the facts that '0' is a neutral element for
   addition and that 'S (n + m) = n + S m' - the facts that we proved 
   before. However, those results are also available in the standard 
   library. First we need to make them available with the
   'Require Import' command. *)
   
Require Import Plus.
Check Nat.add_0_l.
Check Nat.add_0_r.
Check plus_n_Sm.

Lemma plus_comm : forall m n, m + n = n + m.

Proof.
intros.
induction m.
simpl.
rewrite Nat.add_0_r.
reflexivity.
(*step*)
simpl.
rewrite -> IHm.
rewrite plus_n_Sm.
reflexivity.
 
Qed.
