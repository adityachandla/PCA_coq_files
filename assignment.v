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
  | node l v r => if n <=? v then node (insert n l) v r else node l v (insert n r)
  end.

Fixpoint occurs(n: nat)(t: tree): Prop :=
  match t with
    | leaf => False
    | node l v r => v = n \/ occurs n l \/ occurs n r
  end.

Fixpoint sort_insert(l: (list nat))(t: tree) {struct l}: (tree) :=
  match l with
  | nil => t
  | cons x xs => insert x (sort_insert xs t)
  end.

Fixpoint to_list(t: tree): (list nat) :=
  match t with
  | leaf => []
  | node l v r => (to_list l) ++ v::to_list r
  end.

Definition sort(t : tree) : tree :=
  sort_insert (to_list t) leaf.

(* Compute(insert 2 (node leaf 3 leaf)). *)

(*Print Nat.*)

Lemma leq_insert: forall t: tree, forall n n0: nat,
  n <= n0 /\ all_leq n0 t -> all_leq n0 (insert n t).
Proof.
intros.
destruct H.
induction t.
- simpl. auto.
- simpl. simpl in H0.
  destruct H0 as [H1 [H2 H3]].
  destruct (n <=? n1) as []eqn:?.
  * simpl; auto.
  * simpl; auto.
Defined.

Lemma ge_insert: forall t: tree, forall n n0: nat,
  n > n0 /\ all_geq n0 t -> all_geq n0 (insert n t).
Proof.
intros.
destruct H.
induction t.
- simpl. auto.
- simpl. simpl in H0.
  destruct H0 as [H1 [H2 H3]].
  destruct (n <=? n1) as []eqn:?.
  * simpl; auto.
  * simpl; auto.
Defined.

Lemma insert_correctness: forall t: tree, forall n: nat, bst t -> bst (insert n t).
Proof.
intros.
induction t.
* simpl; auto.
* simpl; simpl in H.
  destruct H as [H1 [H2 [H3 H4]]].
  destruct (n <=? n0) as []eqn:?.
  - simpl.
    repeat split.
    apply leq_insert.
    split.
    apply leb_complete in Heqb.
    assumption.
    assumption. 
    assumption.
    apply IHt1; assumption.
    assumption.
  - simpl.
    apply leb_complete_conv in Heqb.
    repeat split.
    assumption.
    apply ge_insert.
    auto.
    assumption.
    apply IHt2; assumption.
Defined.

Compute(sort_insert [3;2;11] leaf).
Compute(insert 2 (node leaf 3 leaf)).


Lemma sort_insert_append_assoc: forall l1 l2: (list nat), forall t: tree,
  sort_insert (l1 ++ l2) t = sort_insert l1 (sort_insert l2 t).
Proof.
intros.
induction t.
- induction l1.
  * auto.
  * simpl.
    rewrite IHl1.
    reflexivity.
- induction l2.
  * simpl.
    rewrite app_nil_r.
    reflexivity.
  * simpl.
  (*TODO*)
Admitted.

Lemma sort_insert_correctness: forall t: tree, forall l: (list nat),
  bst t -> bst (sort_insert l t).
Proof.
intros.
induction l.
- auto.
- simpl.
  apply insert_correctness.
  auto.
Defined.

Lemma sort_result_is_bst: forall t: tree, bst (sort t).
Proof.
intros.
unfold sort.
induction t.
- simpl. tauto.
- simpl.
  rewrite sort_insert_append_assoc.
  simpl.
  apply sort_insert_correctness.
  apply insert_correctness.
  assumption.
Qed.


