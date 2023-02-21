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
  (* copy your definition here *)

(* Now let us define a function 'treeSum' that given a
   tree returns the sum of all the elements in the tree *)

    (**** write the function 'tree_sum' ****)

(* Let us check it on some input *)

Lemma tree_sum_ex : forall a b c d,
  tree_sum (node (node leaf a leaf) b (node (node leaf c leaf) d leaf)) =
  a + b + c + d.
  
Proof.
  (*! proof *)
  
Qed.

(* Now let us prove that the sum of the elements in the
   mirrored tree is the same as in the original one *)
   
Lemma mirror_tree_sum : forall T, tree_sum T = tree_sum (mirror T).

Proof.
  (*! proof *)

Qed.