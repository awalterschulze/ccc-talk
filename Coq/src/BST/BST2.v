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
  | Node l bvalue r =>
    if value < bvalue
    then Node (insert value l) bvalue r
    else
      if bvalue < value
      then Node l bvalue (insert value r)
      else Node l value r
  end.

Theorem contains_insert_prop:
  forall (t : tree) (ivalue: nat),
  contains ivalue (insert ivalue t) = true.
Proof.
nail.
induction_on_tree t.
- evaluate.
  same.
- evaluate.
  compare ivalue tvalue as C.
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
    (* Start here *)
    (* Okay, now I see it is just IHrighty *)
    just IHrighty.
Qed.

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
nail.
induction_on_tree t.
- evaluate.
  split3; easy.
- evaluate.
  destruct AL as [BTC All].
  destruct All as [AllLefty AllRighty].
  specialize (IHlefty AllLefty) as IHlefty.
  specialize (IHrighty AllRighty) as IHrighty.
  compare ivalue tvalue as ITC.
  + evaluate.
    split3.
    * rewrite ITC in BIC. exact BIC.
    * exact AllLefty.
    * exact AllRighty.
  + sub ITC.
    evaluate.
    split3.
    * exact BTC.
    * exact IHlefty.
    * exact AllRighty.
  + sub ITC.
    specialize (Lt_implies_not_Lt ITC) as TIC.
    sub TIC.
    evaluate.
    split3.
    * exact BTC.
    * exact AllLefty.
    * apply IHrighty.
Qed.

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
nail.
induction_on_tree t.
- evaluate.
  wreck; easy.
- evaluate.
  destruct AL as [BTC All].
  destruct All as [AllLefty AllRighty].
  specialize (IHlefty AllLefty) as IHlefty.
  specialize (IHrighty AllRighty) as IHrighty.
  compare ivalue tvalue as ITC.
  + evaluate.
    split3.
    * rewrite ITC in BIC. exact BIC.
    * exact AllLefty.
    * exact AllRighty.
  + sub ITC.
    evaluate.
    split3.
    * exact BTC.
    * exact IHlefty.
    * exact AllRighty.
  + sub ITC.
    specialize (Lt_implies_not_Lt ITC) as TIC.
    sub TIC.
    evaluate.
    split3.
    * exact BTC.
    * exact AllLefty.
    * apply IHrighty.
Qed.

Inductive BST : tree -> Prop :=
  | BST_Nil : BST Nil
  | BST_Node : forall l x r,
    l << x ->
    r >> x ->
    BST l ->
    BST r ->
    BST (Node l x r).

Example is_BST :
  BST (Node (Node Nil 1 Nil) 2 (Node Nil 3 Nil)).
Proof.
constructor.
- evaluate.
  auto.
- evaluate.
  auto.
- constructor.
  + evaluate.
    same.
  + evaluate.
    same.
  + constructor.
  + constructor.
- constructor.
  + evaluate.
    same.
  + evaluate.
    same.
  + constructor.
  + constructor.
Qed.

Example is_not_BST :
  not (BST (Node (Node Nil 3 Nil) 2 (Node Nil 2 Nil))).
Proof.
unfold not.
nail.
inversion H.
inversion H3.
wat.
Qed.

(* Gaurantees that it is correctly constructed: title of the talk *)
Theorem insert_BST : forall (t : tree) (B: BST t) (ivalue : nat),
  BST (insert ivalue t).
Proof.
nail t B.
induction_on_bst B.
- nail.
  evaluate.
  wreck.
  + easy.
  + easy.
  + just BST_Nil.
  + just BST_Nil.
- nail.
  evaluate.
  compare ivalue bvalue as IBC.
  + evaluate.
    wreck.
    * just leftIsLess.
    * just rightIsMore.
    * just BSTl.
    * just BSTr.
  + sub IBC.
    wreck.
    * just (all_less leftIsLess IBC).
    * just rightIsMore.
    * apply IHL.
    * just BSTr.
  + (* And we can prove the same for the right side. *)
    sub IBC.
    sub (Lt_implies_not_Lt IBC).
    wreck.
    * just leftIsLess.
      (*
      forall {ivalue: nat} {t: tree} {bvalue: nat}
        (AL: AllMore t bvalue)
        (BIC: (bvalue < ivalue) = true),
        AllMore (insert ivalue t) bvalue.
      *)
    * just (all_more rightIsMore IBC).
    * just BSTl.
    * apply IHR.
Qed.

Definition BSTinsert
  (ivalue : nat): {t | BST t} -> {t' | BST t'}.
nail.
wreck H into t and P.
exists (insert ivalue t).
(* We have just proved that BST (insert ivalue t), so let's use it. *)
apply insert_BST.
just P.
Defined.