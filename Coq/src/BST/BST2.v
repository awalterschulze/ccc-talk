Require Import ConstructionToolbox.
Require Import Lt.

Inductive tree : Type :=
  | Nil
  | Node (lefty : tree) (value : nat) (righty : tree).

Fixpoint contains (x : nat) (t : tree) : bool :=
  match t with
  | Nil => false
  | Node l y r =>
    if x < y
    then contains x l
    else
      if y < x
      then contains x r
      else x == y
  end.

Fixpoint insert (value: nat) (t : tree) : tree :=
  match t with
  | Nil => Node Nil value Nil
  | Node l tvalue r =>
    if value < tvalue
    then Node (insert value l) tvalue r
    else
      if tvalue < value
      then Node l tvalue (insert value r)
      else Node l value r
  end.

Theorem contains_insert_prop:
  forall (t : tree) (value: nat),
  contains value (insert value t) = true.
Proof.
nail.
induction_on_tree t.
- evaluate.
  same.
- evaluate.
  compare value tvalue as C.
  + evaluate.
    same.
  + sub C.
    evaluate.
    sub C.
    just IHlefty.
  + call (Lt_implies_not_Lt C) as C'.
    sub C'.
    sub C.
    evaluate.
    sub C'.
    sub C.

    (* START HERE *)

    just IHrighty.
Qed.







(* SKIP *)

Fixpoint AllLess (t: tree) (parent: nat) :=
  match t with
  | Nil => True
  | Node l v r =>
    (v < parent = true) /\ AllLess l parent /\ AllLess r parent
  end.

Infix "<<" := AllLess (at level 70).

Theorem all_less:
  forall {ivalue: nat} {t: tree} {bvalue: nat}
  (AL: t << bvalue)
  (BIC: (ivalue < bvalue) = true),
  (insert ivalue t) << bvalue.
Proof.
(* See Proof in BST2_with_notes.v *)
Admitted.

Fixpoint AllMore (t: tree) (parent: nat) :=
  match t with
  | Nil => True
  | Node l v r =>
    (parent < v = true) /\ AllMore l parent /\ AllMore r parent
  end.

Infix ">>" := AllMore (at level 70).

Theorem all_more:
  forall {ivalue: nat} {t: tree} {bvalue: nat}
  (AL: t >> bvalue)
  (BIC: (bvalue < ivalue) = true),
  (insert ivalue t) >> bvalue.
Proof.
(* See Proof in BST2_with_notes.v *)
Admitted.










(* START HERE *)

Inductive isBST : tree -> Prop :=
  | Nil_isBST : isBST Nil
  | Node_isBST : forall l x r,
    l << x ->
    r >> x ->
    isBST l ->
    isBST r ->
    isBST (Node l x r).

Definition BST :=  {t | isBST t}.

Definition BSTinsert
  (ivalue : nat) (bst: BST): BST.
nail.
wreck bst into t and t_isBST.
exists (insert ivalue t).
Abort.

Theorem isBSTinsert : forall (t : tree) (B: isBST t) (ivalue : nat),
  isBST (insert ivalue t).
Proof.
nail t B.
induction_on_is_bst B.
- nail.
  evaluate.
  wreck.
  + easy.
  + easy.
  + just Nil_isBST.
  + just Nil_isBST.
- nail.
  evaluate.
  compare ivalue bvalue as compare_ivalue_bvalue.
  + evaluate.
    wreck.
    * just leftIsLess.
    * just rightIsMore.
    * just isBSTl.
    * just isBSTr.
  + sub compare_ivalue_bvalue.
    wreck.
    * (*
      all_less:
        forall {ivalue: nat} {t: tree} {bvalue: nat}
          (AL: t << bvalue)
          (BIC: (ivalue < bvalue) = true),
        (insert ivalue t) << bvalue.
      *)
      apply all_less.
      --- just leftIsLess.
      --- just compare_ivalue_bvalue.
    * just rightIsMore.
    * apply IHlefty.
    * just isBSTr.
  + (* Same for the right side. *)
    sub compare_ivalue_bvalue.
    sub (Lt_implies_not_Lt compare_ivalue_bvalue).
    wreck.
    * just leftIsLess.
      (*
      forall {ivalue: nat} {t: tree} {bvalue: nat}
        (AL: AllMore t bvalue)
        (BIC: (bvalue < ivalue) = true),
        AllMore (insert ivalue t) bvalue.
      *)
    * just (all_more rightIsMore compare_ivalue_bvalue).
    * just isBSTl.
    * apply IHrighty.
Qed.

Definition BSTinsert
  (ivalue : nat) (bst: BST): BST.
nail.
wreck bst into t and t_isBST.
exists (insert ivalue t).
apply isBSTinsert.
just t_isBST.
Defined.