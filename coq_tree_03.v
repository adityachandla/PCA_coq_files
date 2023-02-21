(* Exercise coq_tree_03 *)

(* Let us start with the definitions from the previous 
   exercises *)

Inductive nat_tree : Set :=
  | leaf : nat_tree
  | node : nat_tree -> nat -> nat_tree -> nat_tree.

Fixpoint mirror (T : nat_tree) : nat_tree :=
  match T with 
  | leaf => leaf
  | node l n r => node (mirror r) n (mirror l)
  end.

(* Now let us prove that taking mirror image of a tree
   twice returs the original tree. *)
    
Lemma mirror_double : forall T, mirror (mirror T) = T.

Proof.

Qed.
