Require Import Arith.
Require Import List.
Import ListNotations.


Section TypeAndFunctionDefinitions.
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
  
  Fixpoint list_min(l: list nat) : option nat:=
    match l with
    | nil => None
    | cons x xs => match list_min xs with
      | None => Some x
      | Some y => Some (Nat.min x y)
      end
    end.
  
  Fixpoint treeMin(t: tree): option nat :=
    match t with
      | leaf => None
      | node l v r => 
        match (treeMin l, treeMin r) with
          | (None, None) => Some v
          | (None, Some y) => Some (Nat.min v y)
          | (Some x, None) => Some (Nat.min v x)
          | (Some x, Some y) => Some (Nat.min v (Nat.min x y))
        end
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

End TypeAndFunctionDefinitions.

(*
Compute(insert 2 (node leaf 3 leaf)).
Compute(sort_insert [3;2;11]).
Compute(insert 2 (node leaf 3 leaf)).
Compute (treeMin (node (node leaf 11 leaf) 3 (node leaf 1 (node leaf 3 leaf)))).

Compute(search 5 (node (node leaf 2 leaf) 5 (node (node leaf 7 leaf) 8 leaf))).
Compute(search 7 (node (node leaf 2 leaf) 5 (node (node leaf 7 leaf) 8 leaf))).
Compute(search 11 (node (node leaf 2 leaf) 5 (node (node leaf 7 leaf) 8 leaf))).
Compute(search 2 (node (node leaf 2 leaf) 5 (node (node leaf 7 leaf) 8 leaf))).
*)

Section PartOneLemmas.


Section InsertLemmas.

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
  Defined.

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

  Lemma insert_retains_elements_back: forall t: tree, forall a n: nat,
     occurs n (insert a t) -> a = n \/ occurs n t.
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

End InsertLemmas.


Section ToListLemmas.
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

End ToListLemmas.


Section SortLemmas.

  Lemma sort_insert_is_bst: forall l: list nat,
    bst (sort_insert l).
  Proof.
  intros.
  induction l.
  - simpl. tauto.
  - simpl.
    apply insert_correctness.
    assumption.
  Defined.

  Lemma sort_result_is_bst: forall t: tree, bst (sort t).
  Proof.
  intros.
  unfold sort.
  induction t.
  - simpl. tauto.
  - apply sort_insert_is_bst.
  Qed.

  Lemma sort_insert_retention: forall n: nat, forall l: (list nat),
    In n l -> occurs n (sort_insert l).
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
    occurs n (sort_insert l) -> In n l.
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
  Defined.

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
  Defined.

  Lemma sort_retention: forall n: nat, forall t: tree,
    occurs n t <-> occurs n (sort t).
  Proof.
  intros.
  split.
  apply sort_retention_forward.
  apply sort_retention_backward.
  Qed.

End SortLemmas.

End PartOneLemmas.

Section PartTwoLemmas.

  Lemma two_min: forall a b c: nat,
    Nat.min a b = c -> a = c \/ b = c.
  Proof.
  intros.
  destruct (Nat.le_ge_cases a b).
  assert (Nat.min a b = a).
   - intuition.
   - rewrite H1 in H.
     auto.
   - assert (Nat.min a b = b).
     intuition.
     rewrite H1 in H.
     auto.
  Defined.

  Lemma three_min: forall a b c d: nat,
    Nat.min a (Nat.min b c) = d -> a = d \/ b = d \/ c = d.
  Proof.
  intros.
  apply two_min in H.
  destruct H.
  - auto.
  - apply two_min in H.
    auto.
  Defined.

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
  Defined.

  Lemma min_element_exists_in_tree: forall t: tree, forall n: nat,
    treeMin t = Some n -> occurs n t.
  Proof.
  intros.
  induction t.
  - inversion H.
  - apply tree_min_breakdown in H.
    destruct H as [H1 | [H2 | H3]]; simpl; auto.
  Defined.

 
  Lemma min_element_smallest: forall t: tree, forall n: nat,
    treeMin t = Some n -> all_geq n t.
  Proof.
  intros.
  induction t.
  - inversion H.
  - simpl in H.
    destruct (treeMin t1) as []eqn:?; destruct (treeMin t2) as []eqn:?.
    * inversion H.
      rewrite H1.
  Admitted.


  Lemma leftmost_element_minimum: forall t: tree,
    bst t -> treeMin t = leftmost t.
  Proof.
  intros.
  induction t.
  - auto.
  - simpl in H.
    destruct H as [H0 [H1[H2 H3]]].
    intuition.
    destruct (treeMin t1) as []eqn:?.
    * destruct (treeMin t2) as []eqn:?.
      + 
  Admitted.

  
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
  Defined.

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
  Defined.

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

End PartTwoLemmas.