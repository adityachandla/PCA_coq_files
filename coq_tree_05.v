(* Exercise coq_tree_05 *)

Require Import Arith.

(* Let us start with the definitions from the previous 
   exercises *)

Inductive nat_tree : Set :=
  | leaf : nat_tree
  | node : nat_tree -> nat -> nat_tree -> nat_tree.

Fixpoint In (n : nat) (T : nat_tree) {struct T} : Prop :=
  match T with
  | leaf => False
  | node l v r => In n l \/ v = n \/ In n r
  end.

Fixpoint mirror (T : nat_tree) : nat_tree :=
  match T with
  | leaf => leaf
  | node l v r => node (mirror r) v (mirror l)
  end. 

Fixpoint tree_sum(T: nat_tree): nat := 
  match T with
  | leaf => 0
  | node l v r => (tree_sum l) + v + (tree_sum r)
  end.

Search (?n + O).

Lemma tree_sum_ex : forall a b c d,
  tree_sum (node (node leaf a leaf) b (node (node leaf c leaf) d leaf)) =
  a + b + c + d.
  
Proof.
intros.
simpl.
repeat rewrite Nat.add_0_r.
rewrite Nat.add_assoc.
reflexivity.
Qed.

Print Nat.add_comm.
(* Now let us prove that the sum of the elements in the
   mirrored tree is the same as in the original one *)
   
Lemma mirror_tree_sum : forall T, tree_sum T = tree_sum (mirror T).

Proof.
  intros.
  induction T.
* simpl; reflexivity.
* simpl.
  rewrite IHT1.
  rewrite IHT2.
  rewrite Nat.add_comm.
  rewrite Nat.add_comm with (m := n).
  rewrite Nat.add_assoc.
  reflexivity.
Qed.