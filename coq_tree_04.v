(* Exercise coq_tree_04 *)

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
  | node l n r => node (mirror r) n (mirror l)
  end.

(* Now let us prove that an element belong to a mirror
   image of a tree if and only if it belongs to the 
   tree itself. *)
   
(* Hint: to see how the iff ("<->") connective is defined 
         in Coq try 'Print iff.'. You can also do 
	 'unfold iff' within the proof. *)
   
Lemma mirror_In_l : forall n T, In n T -> In n (mirror T).
intro n.
induction T.
simpl.
auto.
intro H.
simpl.
simpl in H.
repeat destruct H.
(* destruct H as [H0 | [H1 | H2]]. *)
right.
right.
apply IHT1; auto.
right; left.
auto.
left.
apply IHT2; auto.
Qed.

Lemma mirror_In_r : forall n T, In n (mirror T) -> In n T.
Admitted.

Lemma mirror_In : forall n T, In n T <-> In n (mirror T).

Proof.
intros.
unfold iff.
split.
elim T.
intros.
simpl.
unfold In in H.
contradiction.
intros.
simpl.
simpl In in H1.
destruct H1.
right ; right ; apply H ; exact H1.
destruct H1.
right ; left ; apply H1.
left ; apply H0 ; exact H1.
(* the way back *)
elim T ; intros.
simpl in H ; contradiction.
simpl.
simpl in H1.
destruct H1.
right ; right ; apply H0 ; exact H1.
destruct H1.
right ; left ; exact H1.
left ; apply H ; exact H1.
Qed.
