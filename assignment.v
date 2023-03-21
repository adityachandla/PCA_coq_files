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

Lemma insertion_equality_forward: forall t1 t2: tree, forall a: nat,
  t1 = t2 -> insert a t1 = insert a t2.
Proof.
intros.
induction t1.
- induction t2.
  * reflexivity.
  * rewrite H; reflexivity.
- rewrite H; reflexivity.
Defined.


Lemma insertion_equality: forall t1 t2: tree, forall a: nat,
  insert a t1 = insert a t2 -> t1 = t2.
Proof.
intros.
induction t1.
- simpl in H.
Admitted.

Lemma sort_insert_append_assoc: forall l1 l2: (list nat), forall t: tree,
  sort_insert (l1 ++ l2) t = sort_insert l1 (sort_insert l2 t).
Proof.
intros.
induction l2.
- simpl.
  rewrite app_nil_r.
  reflexivity.
- simpl.
  induction l1.
  * simpl; reflexivity.
  * simpl. simpl in IHl2.
    rewrite IHl1.
    reflexivity.
    apply insertion_equality in IHl2.
    assumption.
Defined.


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

Lemma inserted_element_present: forall t: tree, forall a: nat,
  occurs a (insert a t).
Proof.
intros.
induction t.
- simpl. auto.
- simpl.
  destruct (a <=? n).
  * simpl. right. left. assumption.
  * simpl. right. right. assumption.
Defined.

Lemma insert_retains_elements: forall t: tree, forall a n: nat,
   a = n \/ occurs n t -> occurs n (insert a t).
Proof.
intros.
destruct H.
- rewrite H.
  apply inserted_element_present.
- induction t.
  * simpl in H. simpl. auto.
  * simpl.
    simpl in H.
    destruct H as [H1 | [H2 | H3]].
    + destruct (a <=? n0).
      simpl. auto.
      simpl. auto.
    + destruct (a <=? n0).
      simpl. auto.
      simpl. auto.
    + destruct (a <=? n0).
      simpl. auto.
      simpl. auto.
Defined.

Print or_comm.

Lemma insert_retains_elements_back: forall t: tree, forall a n: nat,
   occurs n (insert a t) -> a = n \/ occurs n t .
Proof.
intros.
induction t.
- simpl in H. destruct H as [H1|[H2|H3]]. auto. auto. auto.
- simpl in H.
  destruct (a <=? n0).
  * simpl in H.
    simpl.
    destruct H as [H1|[H2|H3]].
    + auto.
    + apply or_comm. apply or_assoc. right. 
      apply or_assoc. apply or_comm. apply or_assoc. right.
      auto.
    + apply or_comm. apply or_assoc. right.
      apply or_assoc. right.
      auto.
  * simpl.
    simpl in H.
    destruct H as [H1|[H2|H3]].
    + auto.
    + apply or_comm. apply or_assoc. right.
      apply or_assoc. apply or_comm. apply or_assoc. right.
      auto.
    + apply or_comm. apply or_assoc. right.
      apply or_assoc. right.
      apply or_comm. auto.
Defined.

Lemma sort_insert_retention: forall n: nat, forall l: (list nat),
  In n l -> occurs n (sort_insert l leaf).
Proof.
intros.
induction l.
- auto.
- simpl.
  simpl in H.
  destruct H.
  * apply insert_retains_elements.
    auto.
  * apply insert_retains_elements.
    right. auto.
Defined.

Lemma sort_insert_retention_back: forall n: nat, forall l: (list nat),
  occurs n (sort_insert l leaf) -> In n l.
Proof.
intros.
induction l.
- auto.
- simpl.
  simpl in H.
  apply insert_retains_elements_back in H.
  destruct H.
  * auto.
  * right.
    auto.
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

Lemma to_list_retains_elements_back: forall t: tree, forall x: nat,
  In x (to_list t) -> occurs x t.
Proof.
intros.
induction t.
- auto.
- simpl.
  simpl in H.
  apply in_app_or in H.
  simpl.
  destruct H as [H1|[H2|H3]].
  * auto.
  * left. auto.
  * right. right. auto.
Defined.


Lemma occurs_retention_forward: forall n: nat, forall t: tree,
  occurs n t -> occurs n (sort t).
Proof.
intros.
induction t.
- simpl; simpl in H; assumption.
- simpl in H.
  apply sort_insert_retention.
  destruct H as [H1 | [H2 | H3]].
  * simpl.
    apply in_or_app.
    right.
    rewrite H1.
    apply in_eq.
  * simpl.
    apply in_or_app.
    left.
    apply to_list_retains_elements.
    assumption.
  * simpl.
    apply in_or_app.
    right.
    apply in_cons.
    apply to_list_retains_elements.
    assumption.
Defined.

Lemma occurs_retention_backward: forall n: nat, forall t: tree,
   occurs n (sort t) -> occurs n t.
Proof.
intros.
induction t.
- simpl; simpl in H; assumption.
- simpl.
  apply sort_insert_retention_back in H.
  simpl in H.
  apply in_app_or in H.
  simpl in H.
  destruct H as [H1 | [H2|H3]].
  * right;left.
    apply to_list_retains_elements_back.
    auto.
  * auto.
  * right; right.
    apply to_list_retains_elements_back.
    auto.
Defined.

Lemma occurs_retention: forall n: nat, forall t: tree,
  occurs n t <-> occurs n (sort t).
Proof.
intros.
split.
apply occurs_retention_forward.
apply occurs_retention_backward.
Qed.