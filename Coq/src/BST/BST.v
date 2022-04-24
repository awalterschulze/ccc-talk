(* Set Implicit Arguments. *)
(* Set Asymmetric Patterns. *)

Require Import Coq.Arith.PeanoNat.

(* hide so that we don't have to explain notations *)
Infix "<" := Nat.ltb.
Infix "<=" := Nat.leb.
Notation "a == b" := (Nat.eqb a b) (at level 70).
Notation "x + 1" := (S x) (at level 70).

Tactic Notation "induction_on_tree" constr(T) :=
  induction T as [| lefty IHlefty tvalue righty IHrighty].
Tactic Notation "induction_on_bst" constr(B) :=
  induction B as [| l bvalue r leftIsLess rightIsMore BSTl IHL BSTr IHR].
Ltac split3 := split; [| split].

Tactic Notation "nail" := intros.
Tactic Notation "nail" ident(H1) ident(H2) := intros H1 H2.
Tactic Notation "nail" ident(H1) ident(H2) ident(H3) := intros H1 H2 H3.
Tactic Notation "wreck" :=  constructor.
Tactic Notation "wreck" constr(H) :=  destruct H.
Tactic Notation "wreck" constr(H) "into" ident(H1) "and" ident(H2) := destruct H as [H1 H2].
Tactic Notation "wreck" constr(H) "into" ident(H1) "," ident(H2) "and" ident(H3) := injection H; intros H3 H2 H1.
Tactic Notation "just" constr(H) := exact H.
Tactic Notation "same" := reflexivity.
Tactic Notation "wat" := discriminate.
Tactic Notation "call" constr(B) "as" ident(A) :=
  specialize B as A.
Tactic Notation "sub" constr(A) :=
  rewrite A.
Tactic Notation "unapply" constr(A) := apply A.

Ltac evaluate := repeat (simpl || rewrite Nat.ltb_irrefl || rewrite Nat.eqb_refl).

(* hide so that we  don't have to explain ltac *)
Ltac case_cmp x y C :=
  remember (Nat.compare x y) as C;
  match goal with
  | [ C: comparison |- _ ] =>
    induction C
  end;
  match goal with
  | [ H : Eq = _ |- _ ] =>
    rename H into C;
    symmetry in C;
    apply Nat.compare_eq in C;
    rewrite C
  | [ H : Lt = _ |- _ ] =>
    rename H into C;
    symmetry in C;
    rewrite Nat.compare_lt_iff in C;
    rewrite <- Nat.ltb_lt in C
  | [ H : Gt = _ |- _ ] =>
    rename H into C;
    symmetry in C;
    rewrite Nat.compare_gt_iff in C;
    rewrite <- Nat.ltb_lt in C
  end.

Tactic Notation "compare" constr(X) constr(Y) "as" ident(C) :=
  case_cmp X Y C.

(* hide so that we don't have to explain Prop *)
Lemma ltb_ge:
  forall {x: nat} {y: nat}, (y <= x) = true -> (x < y) = false.
Proof.
nail.
apply Nat.ltb_ge.
rewrite Nat.leb_le in H.
assumption.
Qed.

(* hide so that we don't have to explain Prop *)
Lemma le_neq:
  forall {x: nat} {y: nat}, (x < y = true) -> (x <= y = true) /\ x == y = false.
Proof.
nail.
rewrite Nat.leb_le.
rewrite Nat.eqb_neq.
rewrite Nat.ltb_lt in H.
apply Nat.le_neq.
assumption.
Qed.

(* a basic proofs of lt *)
Lemma Lt_implies_Leq:
  forall {x: nat} {y: nat},
  (x < y = true) -> (x <= y = true).
Proof.
nail.
Search (?X < ?Y = true).
call (le_neq H) as H'.
wreck H' into Leq and Eq.
just Leq.
Qed.

(* a basic proofs of lt *)
Lemma Lt_implies_not_Lt:
  forall {x: nat} {y: nat},
  (x < y) = true
  -> y < x = false.
Proof.
(* Let's nail this to the wall using Walter's hammer *)
nail.
(* We can explore all cases of the comparison *)
compare x y as C.
- (* Let's focus on case 1, where x = y *)
  (* Here we can search Coq's toolbox for an appropriate tool *)
  SearchRewrite (?X < ?X).
  (* We can substitute using (x < x) = false *)
  sub Nat.ltb_irrefl.
  (* And now the left and the right side of the equality are the same. *)
  same.
- (* Now let's focus on case 2, where x < y *)
  (* Earlier I proved ltb_ge: (y <= x) = true -> (x < y) = false *)
  (* The goal does application in reverse *)
  (* So if we have the return type, we can get the input type *)
  apply ltb_ge.
  (* Now we can apply the theorem we proved before *)
  (* (x < y = true) -> (x <= y = true) *)
  (* Here again the goal does application in reverse *)
  (* So if we have the return type, we can get the input type *)
  apply Lt_implies_Leq.
  (* Oh and this is just C *)
  just C.
- (* And then we can prove the final case. *)
  apply ltb_ge.
  apply Lt_implies_Leq.
  just H.
(* Qed checks that there is nothing else to prove *)
(* That means the prove is complete. *)
Qed.

(* Show side by side Kotlin implementation *)
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

Example ex_tree_1 :=
  Node Nil 1 Nil.

Theorem Contains1:
  contains 1 ex_tree_1 = true.
Proof.
(* There is nothing I can nail to the wall. *)
(* But it seems like we should be able to evaluate this. *)
evaluate.
(* So the contains evaluated to true. *)
(* And now the right and left side look the same. *)
same.
(* Let me ask Coq if I finished the proof *)
Qed.
(* All green, seems I did a proof thing. *)

Theorem ContainsNested1:
  forall (t: tree), t = Node ex_tree_1 2 (Node Nil 3 Nil) -> contains 1 t = true.
Proof.
(* I have something for the assitant to the prover *)
(* Lend me your hammer here *)
(* Walter: You can have my hammer. *)
nail.
(* We need to break down the tree, let's wreck it *)
wreck t.
- (* Well Nil can't be equal to a bigger tree, wat! *)
  wat.
- (* Let's strip of the constructor from both sides in H *)
  wreck H into Ht1, Hv and Ht2.
  (* Now we can do a substitution *)
  sub Hv.
  (* This seems like something Coq should be able to evaluate *)
  evaluate.
  (* Let's also substitute Ht1 *)
  sub Ht1.
  (* Hey this is the proof Walter did, sometimes he is useful *)
  just Contains1.
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

Theorem contains_insert_eq : forall (t : tree) (value: nat),
  contains value (insert value t) = true.
Proof.
(* Let's nail some things on the wall. *)
nail.
(*
Now we have to do some math.
Some of you might remember induction.
This is the tool we use for recursive structures.
*)
induction_on_tree t.
-
(* Coq can figure this part out *)
evaluate.
same.
-
  (* I think Coq can evaluate this a bit, to take us forward. *)
  evaluate.
  (* There seems to be a lot of comparisons, so lets compare. *)
  compare value tvalue as C.
  (* Let's look at the first case *)
  +
    (* Well tvalue < tvalue is false, so let's evaluate a bit. *)
    evaluate.
    (* Oh that solves it *)
    same.
  + (* We know value < tvalue = true, so we can substitute that. *)
    sub C.
    (* Let's try evaluate. *)
    evaluate.
    (* Oh interesting, I see there is another thing we can substitute *)
    sub C.
    (* Hmmm, Ah I have see IHlefty is exactly the goal. *)
    just IHlefty.
  + (* I see something we can substitute *)
    sub C.
    (* Hmmm, I know that if tvalue < value then value is not smaller than tvalue *)
    (* I think we did this proof before. *)
    (* Yes it was called Lt_implies_not_Lt *)
    (* So we can call it with C and add it to our assumptions. *)
    call (Lt_implies_not_Lt C) as C'.
    (* Nice, now we can substitute it. *)
    sub C'.
    (* I don't know what to do, so let's try evaluate. *)
    evaluate.
    (* Yeah I think we can substitute these comparisons. *)
    sub C'.
    sub C.
    (* Hmmm, I should be able to use IHrighty, but it doesn't look right *)
    (* Walter I think you Coq'd up *)
    (* I don't there is any way to complete this proof in Coq that will compile. *)

(* TODO: Move to different file and put a lot of spaces, so you can't see Abort on the screen.  *)

    Fail (just IHrighty).
Abort.

Fixpoint bst_insert (value: nat) (t : tree) : tree :=
  match t with
  | Nil => Node Nil value Nil
  | Node l bvalue r =>
    if value < bvalue
    then Node (bst_insert value l) bvalue r
    else
      if bvalue < value
      then Node l bvalue (bst_insert value r)
      else Node l value r
  end.

Theorem lookup_bst_insert_eq:
  forall (t : tree) (ivalue: nat),
  contains ivalue (bst_insert ivalue t) = true.
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
  (bst_insert ivalue t) << bvalue.
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
  (bst_insert ivalue t) >> bvalue.
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
  BST (bst_insert ivalue t).
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
        AllMore (bst_insert ivalue t) bvalue.
      *)
    * just (all_more rightIsMore IBC).
    * just BSTl.
    * apply IHR.
Qed.

Definition BSTinsert
  (ivalue : nat): {t | BST t} -> {t' | BST t'}.
nail.
wreck H into t and P.
exists (bst_insert ivalue t).
(* We have just proved that BST (bst_insert ivalue t), so let's use it. *)
apply insert_BST.
just P.
Defined.