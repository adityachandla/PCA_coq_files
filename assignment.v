Require Import Arith.
Require Import List.
Import ListNotations.

Inductive tree : Set :=
| leaf : tree
| node : tree -> nat -> tree -> tree.

Fixpoint all_leq(n: nat)(t: tree): Prop :=
  match t with
    | leaf => True
    | node l val r => (val <= n) /\ (all_leq n l) /\ (all_leq n r)
  end.

Fixpoint all_geq(n: nat)(t: tree): Prop := 
  match t with
    | leaf => True
    | node l val r => (val > n) /\ (all_geq n l) /\ (all_geq n r)
  end. 

Fixpoint bst (T: tree): Prop :=
  match T with
  | leaf => True
  | node l v r => (all_leq v l) /\ (all_geq v r) /\ bst l /\ bst r
end.

Fixpoint insert(n: nat)(T: tree): tree :=
  match T with
  | leaf => node leaf n leaf
  | node l v r => if Nat.leb n v then (insert n l) else (insert n r)
  end.

(*Print Nat.*)

Lemma insert_correctness: forall t: tree, forall n: nat, bst t -> bst (insert n t).
Proof.
intros.
induction t.
* simpl.
  auto.
* simpl insert.
  destruct (n <=? n0).
  apply IHt1.
  destruct H as [H1 [H2 [H3 H4]]].
  auto.
  apply IHt2.
  destruct H as [H1 [H2 [H3 H4]]].
  auto.
Qed.

Fixpoint occurs(n: nat)(t: tree): Prop :=
  match t with
    | leaf => False
    | node l v r => v = n \/ occurs n l \/ occurs n r
  end.

Fixpoint to_list(T: tree): (list nat) :=
  match T with
    | leaf => nil
    | node l v r => (to_list l) ++  v::(to_list r)
  end.

Lemma list_tree_equality: forall t1 t2: tree, forall n: nat, 
  to_list (node t1 n t2) = (to_list t1) ++ n::(to_list t2).
Proof.
intros.
induction t1.
  * induction t2.
    simpl; reflexivity.
    simpl. reflexivity.
  * induction t2.
    simpl. reflexivity.
    simpl; reflexivity.
Defined.



Lemma to_list_retains_elements: forall t: tree, forall x: nat,
  occurs x t -> In x (to_list t).
Proof.
intros.
induction t.
- simpl. simpl in H. assumption.
- simpl in H.
  destruct H.
  * rewrite H.
    simpl.
    apply in_elt.
  * destruct H.
    + simpl.
      apply in_or_app.
      left; apply IHt1; assumption.
    + simpl.
      apply in_or_app.
      right.
      apply in_cons.
      apply IHt2; assumption.
Defined.


Fixpoint insert_sorted(l: (list nat))(ele: nat): (list nat) :=
  match l with
    | nil => [ele]
    | cons x xs => if x <? ele then [x] ++ (insert_sorted xs ele) 
      else ele::x::nil ++ xs
  end.

Lemma insert_sorted_retains_elements: forall l :(list nat), forall x n: nat,
  In x l -> In x (insert_sorted l n).
Proof.
intros.
induction l.
- simpl; right; contradiction.
- simpl.
  destruct (a <? n).
  * simpl.
    simpl in H.
    destruct H as [H1 | H2].
    left; assumption.
    right; apply IHl; assumption.
  * simpl; simpl in H.
    destruct H as [H1 | H2].
    right; left; assumption.
    right; right; assumption.
Defined.

Lemma insert_sorted_inserts_element: forall l: (list nat), forall n: nat,
  In n (insert_sorted l n).
Proof.
intros.
induction l.
- simpl. left. reflexivity.
- simpl.
  destruct (a <? n).
  * simpl; right; assumption.
  * simpl. left. reflexivity.
Defined.
  
  
Fixpoint sort_list(l: (list nat)): (list nat) :=
  match l with
    | nil => nil
    | cons x xs => insert_sorted (sort_list xs) x
  end.

(*
Compute(sort_list (5::1::3::2::nil)).
Compute(sort_list nil).
Compute(sort_list (22::22::11::11::5::1::2::nil)).
*)


Lemma sorted_list_contains_elements: forall l: (list nat), forall n: nat,
  In n l -> In n (sort_list l).
Proof.
intros.
induction l.
- simpl; auto.
- simpl.
  simpl in H.
  destruct H.
  * rewrite H.
    apply insert_sorted_inserts_element.
  * apply insert_sorted_retains_elements.
    apply IHl.
    assumption.
Defined.

Fixpoint to_tree(l: (list nat)): tree :=
  match l with
    | nil => leaf
    | cons x xs => node leaf x (to_tree xs)
  end.

Definition sort(t: tree): tree :=
  to_tree (sort_list (to_list t)).

(*
Compute(sort (node (node leaf 11 leaf) 44 (node leaf 1 leaf))).
Compute(sort (node leaf 1 (node leaf 2 (node leaf 3 leaf)))).
*)



(*sort_list (to_list t1 ++ n :: to_list t2))*)

Lemma occurs_bst_forward: forall t: tree, forall x: nat,
  occurs x t -> occurs x (sort t).
Proof.
intros.
unfold sort.


Lemma sort_result_bst: forall t: tree, bst (sort t).
Proof.
intros.
unfold sort.
(* then here *)

