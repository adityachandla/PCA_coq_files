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

Fixpoint occurs_list(l: (list nat))(v: nat): Prop :=
  match l with
    | nil => False
    | cons x xs => x = v \/ occurs_list xs v
  end.


Fixpoint insert_sorted(l: (list nat))(ele: nat): (list nat) :=
  match l with
    | nil => [ele]
    | cons x xs => if x <? ele then [x] ++ (insert_sorted xs ele) 
      else ele::x::nil ++ xs
  end.

Lemma insert_sorted_retains_elements: forall l :(list nat), forall x n: nat,
  occurs_list l x -> occurs_list (insert_sorted l n) x.
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
  occurs_list (insert_sorted l n) n.
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

Lemma element_in_sublist: forall l: (list nat), forall a n : nat,
  occurs_list l n -> occurs_list (a::l) n.
Proof.
intros.
induction l.
- simpl in H. simpl. right. assumption.
- simpl.
(*Left here*)


Lemma sorted_list_contains_elements: forall l: (list nat), forall n: nat,
  occurs_list l n -> occurs_list (sort_list l) n.
Proof.
intros.
induction l.
- simpl; auto.
- simpl.
  apply insert_sorted_retains_elements.
  apply IHl.
(*Then here*)



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

Lemma sort_result_bst: forall t: tree, bst (sort t).
Proof.
intros.
induction t.
* simpl. auto.
* unfold sort.
  unfold sort in IHt1; unfold sort in IHt2.
  rewrite list_tree_equality.
(* then here *)

