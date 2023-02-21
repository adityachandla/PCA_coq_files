
(* Exercise coq_tree_01 *)

(* Let us define binary tree of natural numbers.
   Such a tree is either a leaf, or an internal
   node with some natural number and two subtrees. *)
Inductive nat_tree : Set :=
  | leaf : nat_tree
  | node : nat_tree -> nat -> nat_tree -> nat_tree.

(* Now let us define the 'In n T' predicate that returns
   a proposition indicating whether a tree 'T' contains 
   a natural number 'n' *)
Fixpoint In (n : nat) (T : nat_tree) {struct T} : Prop :=
  match T with
  | leaf => False
  | node l v r => In n l \/ v = n \/ In n r
  end.
  
(* Now let us prove that if an element 'n' belongs to
   this particular tree:
   
       b
      /
     a

   then 'n' either equals 'a' or 'b'. *)

Lemma tree2_In : forall n a b, 
  In n (node (node leaf a leaf) b leaf) ->
  n = a \/ n = b.
  
Proof.

Qed.
