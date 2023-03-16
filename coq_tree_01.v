
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
  intros.
  destruct H.
  left.
  destruct H.
  absurd (In n leaf).
  contradiction.
  simpl.
  contradiction.
  destruct H.
  rewrite H.
  reflexivity.
  absurd (In n leaf); contradiction; simpl.
  right.  
  destruct H.
  rewrite H.
  reflexivity.
  absurd (In n leaf); contradiction; simpl.
Qed.

(*
  Done in lectures as well.
  symetric
*)


Lemma tree3_In : forall t1 t2 : nat_tree, forall n b: nat, In n (node (t1 b t2)) ->
   In a t1 \/ In b t2 \/ n = b.
Proof.
Admitted.
  


Lemma tree2_In' : forall n a b, 
  In n (node (node leaf a leaf) b leaf) ->
  n = a \/ n = b.
  
Proof.
  intros.
  simpl in H.
Qed.