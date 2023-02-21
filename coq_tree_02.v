(* Exercise coq_tree_02 *)

(* Let us start with the definition of a binary tree of
   natural numbers, from the previous exercise *)

Inductive nat_tree : Set :=
  | leaf : nat_tree
  | node : nat_tree -> nat -> nat_tree -> nat_tree.

Print plus.

(* Now define the function 'mirror' that return a mirror
   image of a tree.
   For instance:
   
               a              a
             /   \          /   \
   mirror(  b     d   ) =  d     b
   	     \    /\       /\   /
	      c  e  f     f  e c
*)

Fixpoint mirror (T : nat_tree) : nat_tree :=
  match T return nat_tree with 
  | leaf => leaf 
  | node l n r => node (mirror r) n (mirror l) 
  end.
  
(* Now, let us check this function on the example presented 
   above *)
   
Lemma mirror_ex : forall a b c d e f,
  mirror (node
      (node leaf b (node leaf c leaf)) 
      a
      (node (node leaf e leaf) d (node leaf f leaf))) =
  node
    (node (node leaf f leaf) d (node leaf e leaf))
    a
    (node (node leaf c leaf) b leaf).

Proof.
intros.
unfold mirror.
reflexivity.
Qed.
