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

Example example :=
  Node Nil 1 Nil.

Theorem ExampleTreeContains1:
  contains 1 example = true.
Proof.
evaluate.
same.
Qed.

Theorem NestedTreeContains1:
  forall (t: tree), t = Node example 2 (Node Nil 3 Nil) -> contains 1 t = true.
Proof.
nail.
wreck t.
- wat.
- wreck H into Ht1, Hv and Ht2.
  sub Hv.
  evaluate.
  sub Ht1.
  just ExampleTreeContains1.
Qed.

Fixpoint insert (value : nat) (t : tree) : tree :=
  match t with
  | Nil => Node Nil value Nil
  | Node l tvalue r =>
    if value < tvalue
    then Node (insert value l) tvalue r
    else
      if tvalue < value
      then Node l tvalue (insert tvalue r)
      else Node l value r
  end.

Theorem contains_insert_prop : forall (t : tree) (value: nat),
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
  + sub C.
    call (Lt_implies_not_Lt C) as C'.
    sub C'.
    evaluate.
    sub C'.
    sub C.












































































































































































    Fail (just IHrighty).
Abort.
