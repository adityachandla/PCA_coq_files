Require Import Arith.
Require Import List.
Import ListNotations.

(** Inductive definitions and methods for both Part 1 and Part 2 *)
  Inductive tree : Set :=
  | leaf : tree
  | node : tree -> nat -> tree -> tree.

  Fixpoint all_leq(n: nat)(t: tree): Prop :=
    match t with
      | leaf => True
      | node l val r => (val <= n) /\ (all_leq n l) /\ (all_leq n r)
    end.

  Fixpoint all_gr(n: nat)(t: tree): Prop := 
    match t with
      | leaf => True
      | node l val r => (val > n) /\ (all_gr n l) /\ (all_gr n r)
    end. 

  Fixpoint all_geq(n: nat)(t: tree): Prop := 
    match t with
      | leaf => True
      | node l v r => (v >= n) /\ (all_geq n l) /\ (all_geq n r)
    end.

  Fixpoint bst (T: tree): Prop :=
    match T with
    | leaf => True
    | node l v r => (all_leq v l) /\ (all_gr v r) /\ bst l /\ bst r
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

  Fixpoint sort_insert(l: list nat): (tree) :=
    match l with
    | nil => leaf
    | cons x xs => insert x (sort_insert xs)
    end.

  Fixpoint to_list(t: tree): (list nat) :=
    match t with
    | leaf => []
    | node l v r => (to_list l) ++ v::to_list r
    end.

  Definition sort(t : tree) : tree :=
    sort_insert (to_list t).

  Definition omin(a: nat)(b: option nat): nat :=
    match b with
      | None => a
      | Some bv => Nat.min a bv
    end.
  
  Fixpoint treeMin(t: tree): option nat :=
    match t with
      | leaf => None
      | node l v r => Some (omin (omin v (treeMin l))(treeMin r))
    end.

  Fixpoint leftmost(t: tree): option nat :=
    match t with
    | leaf => None
    | node l v r => match leftmost l with
      | None => Some v
      | Some y => Some y
      end
    end.
  
  Fixpoint search(n: nat)(t: tree): Prop :=
    match t with
    | leaf => False
    | node l v r => match Nat.compare n v with
      | Lt => search n l
      | Eq => True
      | Gt => search n r
      end
    end.


(** * Part 1
 *)

(** ** Lemmas related to insert function
*)

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
  Qed.

  Lemma gr_insert: forall t: tree, forall n n0: nat,
    n > n0 /\ all_gr n0 t -> all_gr n0 (insert n t).
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
  Qed.

  Lemma insert_correctness: forall t: tree, forall n: nat, 
    bst t -> bst (insert n t).
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
      apply gr_insert.
      auto.
      assumption.
      apply IHt2; assumption.
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
  Qed.

  Lemma insert_retains_elements_back: forall t: tree, forall a n: nat,
     occurs n (insert a t) -> a = n \/ occurs n t.
  Proof.
  intros.
  induction t.
  - simpl in H. destruct H as [H1|[H2|H3]]; intuition.
  - simpl in H.
    destruct (a <=? n0).
    * simpl in H.
      simpl.
      destruct H as [H1|[H2|H3]]; intuition.
    * simpl.
      simpl in H.
      destruct H as [H1|[H2|H3]]; intuition.
  Qed.

(** ** Lemmas related to to_list function
*)

  Lemma to_list_retains_elements: forall t: tree, forall x: nat,
    occurs x t -> In x (to_list t).
  Proof.
  intros.
  induction t.
  - simpl. simpl in H. assumption.
  - simpl in H.
    destruct H as [H1|[H2|H3]]; simpl; try apply in_or_app; intuition.
    rewrite H1.
    simpl.
    intuition.
  Qed.

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
    destruct H as [H1|[H2|H3]]; auto.
  Qed.

(** ** Lemmas related to sort function
*)

  Lemma sort_insert_is_bst: forall l: list nat,
    bst (sort_insert l).
  Proof.
  intros.
  induction l.
  - simpl. tauto.
  - simpl.
    apply insert_correctness.
    assumption.
  Qed.

  Lemma sort_result_is_bst: forall t: tree, 
    bst (sort t).
  Proof.
  intros.
  unfold sort.
  apply sort_insert_is_bst.
  Qed.

  Lemma sort_insert_retention: forall n: nat, forall l: (list nat),
    In n l -> occurs n (sort_insert l).
  Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    simpl in H.
    destruct H; apply insert_retains_elements; intuition.
  Qed.

  Lemma sort_insert_retention_back: forall n: nat, forall l: (list nat),
    occurs n (sort_insert l) -> In n l.
  Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    simpl in H.
    apply insert_retains_elements_back in H.
    destruct H; intuition.
  Qed.

  Lemma sort_retention_forward: forall n: nat, forall t: tree,
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
  Qed.

  Lemma sort_retention_backward: forall n: nat, forall t: tree,
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
  Qed.

  Lemma sort_retention: forall n: nat, forall t: tree,
    occurs n t <-> occurs n (sort t).
  Proof.
  intros.
  split.
  apply sort_retention_forward.
  apply sort_retention_backward.
  Qed.


(** * Part 2
*)

  (** Minimum element exists in the tree lemmas *)
  Lemma two_min: forall a b c: nat,
    Nat.min a b = c -> a = c \/ b = c.
  Proof.
  intros.
  destruct (Nat.le_ge_cases a b).
  assert (Nat.min a b = a).
   - apply Nat.min_l in H0. assumption.
   - rewrite H1 in H.
     auto.
   - assert (Nat.min a b = b).
     apply Nat.min_l in H0.
     rewrite Nat.min_comm in H0.
     assumption.
     rewrite H1 in H.
     auto.
  Qed.

  Lemma three_min: forall a b c d: nat,
    Nat.min (Nat.min b c) a = d -> a = d \/ b = d \/ c = d.
  Proof.
  intros.
  apply two_min in H.
  destruct H.
  - apply two_min in H; auto.
  - auto.
  Qed.

  Lemma tree_min_breakdown: forall t1 t2: tree, forall n p: nat,
    treeMin (node t1 n t2) = Some p -> Some p = treeMin t1 \/ Some p = treeMin t2 \/ p = n.
  Proof.
  intros.
  simpl in H.
  destruct (treeMin t1).
  - destruct (treeMin t2).
    * inversion H.
      rewrite H1.
      apply three_min in H1.
      destruct H1 as [h2 | [h3 | h4]]; auto.
    * inversion H.
      rewrite H1.
      apply two_min in H1.
      destruct H1; auto.
  - destruct (treeMin t2).
    * inversion H.
      rewrite H1.
      apply two_min in H1.
      destruct H1; auto.
    * inversion H.
      auto.
  Qed.

  Lemma min_element_exists_in_tree: forall t: tree, forall n: nat,
    treeMin t = Some n -> occurs n t.
  Proof.
  intros.
  induction t.
  - inversion H.
  - apply tree_min_breakdown in H.
    destruct H as [H1 | [H2 | H3]]; simpl; auto.
  Qed.

  (** Minimum element minimum*)
  Lemma omin_eq_geq: forall a b c: nat,
    omin a (Some b) = c -> a >= c /\ b >= c.
  Proof.
  Admitted.

  Lemma omin_select: forall a b c: nat,
    omin a (Some b) = c -> a = c \/ b = c.
  Proof.
  Admitted.

  Lemma omin_geq_geq: forall a b c: nat,
    omin a (Some b) >= c -> a >= c /\ b >= c.
  Proof.
  Admitted.

  Lemma geq_trans: forall t: tree, forall p n: nat,
    all_geq n t -> p <= n -> all_geq p t.
  Proof.
  Admitted.

  Lemma min_element_smallest: forall t: tree, forall n: nat,
    treeMin t = Some n -> all_geq n t.
  Proof.
  intros.
  induction t.
  - inversion H; auto.
  - destruct (treeMin t1) as []eqn:?; destruct (treeMin t2) as []eqn:?.
    * inversion H.
      rewrite H1.
      simpl.
      rewrite Heqo in H1.
      rewrite Heqo0 in H1.
      apply omin_eq_geq in H1; destruct H1.
      apply omin_geq_geq in H0.
      repeat split; intuition.
  Admitted.

  (** Leftmost element minimum lemmas *)
  

  Lemma all_leq_occurs: forall t: tree,forall n n1: nat,
    occurs n t -> all_leq n1 t -> n <= n1.
  Proof.
  intros.
  induction t.
  - simpl in H. contradiction.
  - simpl in H.
    simpl in H0.
    destruct H0 as [H1[H2 H3]].
    destruct H as [H4|[H5|H6]]; intuition.
    rewrite <- H4.
    assumption.
  Qed.

  Lemma all_ge_occurs: forall t: tree,forall n n1: nat,
    occurs n t -> all_gr n1 t -> n > n1.
  Proof.
  intros.
  induction t.
  - simpl in H. contradiction.
  - simpl in H.
    simpl in H0.
    destruct H0 as [H1[H2 H3]].
    destruct H as [H4|[H5|H6]];intuition.
    rewrite <- H4.
    assumption.
  Qed.
  
  Lemma tree_min_none: forall t: tree,
    treeMin t = None -> t = leaf.
  Proof.
  intros.
  induction t; intuition.
  simpl in H.
  discriminate H.
  Qed.

  Lemma minimum_element_left_subtree: forall n: nat, forall t1 t2: tree,
    bst(node t1 n t2) -> t1 <> leaf -> treeMin t1 = treeMin (node t1 n t2).
  Proof.
  intros.
  simpl in H.
  destruct H as [H1[H2 [H3 H4]]].
  simpl.
  destruct (treeMin t1) as []eqn:?.
  - destruct (treeMin t2) as []eqn:?.
    * simpl.
      apply min_element_exists_in_tree in Heqo.
      apply min_element_exists_in_tree in Heqo0.
      assert (n1 > n).
      apply all_ge_occurs with (t:=t2);intuition.
      assert (n0 <= n).
      apply all_leq_occurs with (t:=t1); intuition.
      assert (n1 > n0).
      apply Arith_prebase.gt_le_trans_stt with (m:=n); assumption.
      apply Nat.min_l in H5.
      rewrite Nat.min_comm in H5.
      rewrite H5.
      assert (Nat.min n0 n1 = n0); intuition.
    * simpl.
      apply min_element_exists_in_tree in Heqo.
      assert (n0 <= n).
      apply all_leq_occurs with (t:=t1); intuition.
      apply Nat.min_l in H.
      rewrite Nat.min_comm in H.
      intuition.
  - simpl.
    intuition.
    destruct H0.
    apply tree_min_none; assumption.
  Qed.


  Lemma all_gr_gr: forall n n1: nat, forall t: tree,
    all_gr n t -> occurs n1 t -> n < n1.
  Proof.
  intros.
  induction t.
  - simpl in H0. contradiction.
  - simpl in H0.
    simpl in H.
    destruct H as [H1 [H2 H3]].
    destruct H0 as [H4|[H5|H6]].
    * rewrite <- H4; intuition.
    * intuition.
    * intuition.
  Qed.

  Lemma minimum_element_empty_subtree: forall n: nat, forall t1 t2: tree,
    bst(node t1 n t2) -> t1 = leaf -> Some n = treeMin (node t1 n t2).
  Proof.
  intros.
  rewrite H0.
  simpl.
  simpl in H.
  destruct H as [H1[H2 [H3 H4]]].
  destruct (treeMin t2) as []eqn:?.
  - unfold omin.
    apply min_element_exists_in_tree in Heqo.
    assert (n < n0).
    apply all_gr_gr with (t := t2); intuition.
    apply Nat.lt_le_incl in H.
    rewrite Nat.min_l; intuition.
  - intuition.
  Qed.

  Lemma leftmost_empty: forall t: tree,
    leftmost t = None -> t = leaf.
  Proof.
  intros.
  induction t.
  - reflexivity.
  - simpl in H.
    destruct (leftmost t1) as []eqn:?;inversion H. 
  Qed.

  Lemma leftmost_element_minimum: forall t: tree, forall n: nat,
    bst t -> treeMin t = Some n -> leftmost t = Some n.
  Proof.
  intros.
  induction t.
  - inversion H; intuition.
  - simpl.
    destruct (leftmost t1) as []eqn:?.
    * apply IHt1.
      simpl in H; intuition.
      rewrite <- H0.
      apply minimum_element_left_subtree;intuition.
      rewrite H1 in Heqo.
      inversion Heqo.
    * rewrite <- H0.
      apply minimum_element_empty_subtree; intuition.
      apply leftmost_empty; intuition.
  Qed.

  (** Search correctness lemmas *)
  Lemma leq_occurs: forall n v: nat, forall t: tree,
    all_leq v t -> occurs n t -> n <= v.
  Proof.
  intros.
  induction t.
  - simpl in H0. contradiction.
  - simpl in H.
    destruct H as [H1[H2 H3]].
    simpl in H0.
    destruct H0 as [H4|[H5|H6]]; try rewrite H4 in H1; intuition.
  Qed.

  Lemma gr_occurs: forall n v: nat, forall t: tree,
    all_gr v t -> occurs n t -> v < n.
  Proof.
  intros.
  induction t.
  - simpl in H0. contradiction.
  - simpl in H.
    destruct H as [H1[H2 H3]].
    simpl in H0.
    destruct H0 as [H4|[H5|H6]]; try rewrite H4 in H1; intuition.
  Qed.
  

  Lemma search_correct_forward: forall t: tree, forall n: nat,
    bst t -> (occurs n t -> search n t).
  Proof.
  intros.
  induction t.
  - simpl. auto.
  - destruct H as [H1[H2[H3 H4]]].
    simpl in H0.
    destruct H0 as [H5|[H6|H7]].
    * simpl.
      rewrite H5.
      rewrite Nat.compare_refl.
      auto.
    * simpl.
      assert (n <= n0).
      apply leq_occurs with (t := t1); assumption.
      destruct (n ?= n0) as []eqn:?; intuition.
      apply nat_compare_Gt_gt in Heqc.
      apply Nat.lt_nge in H.
      contradiction.
      assumption.
    * simpl.
      assert (n > n0).
      apply gr_occurs with (t := t2); assumption.
      destruct (n ?= n0) as []eqn:?; intuition.
      apply nat_compare_Lt_lt in Heqc.
      apply Nat.lt_ngt in H.
      contradiction.
  Qed.

  Lemma search_correct_backwards: forall t: tree, forall n: nat,
    bst t -> (search n t -> occurs n t).
  Proof.
  intros.
  induction t.
  - auto.
  - simpl in H.
    destruct H as [H1 [H2 [H3 H4]]].
    intuition.
    simpl.
    simpl in H0.
    destruct (n ?= n0) as []eqn:?.
    * apply nat_compare_eq in Heqc. auto.
    * auto.
    * auto.
  Qed.

  Lemma search_correct: forall t: tree, forall n: nat,
    bst t -> (search n t <-> occurs n t).
  Proof.
  intros.
  split.
  apply search_correct_backwards.
  assumption.
  apply search_correct_forward.
  assumption.
  Qed.