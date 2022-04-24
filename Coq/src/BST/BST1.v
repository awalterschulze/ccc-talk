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
(* There is nothing I can nail to the wall. *)
(* But it seems like we should be able to evaluate this. *)
evaluate.
(* So the contains evaluated to true. *)
(* And now the right and left side look the same. *)
same.
(* Let me ask Coq if I finished the proof *)
Qed.
(* All green, seems I did a proof thing. *)

Theorem NestedTreeContains1:
  forall (t: tree), t = Node example 2 (Node Nil 3 Nil) -> contains 1 t = true.
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









































































































































    Fail (just IHrighty).
Abort.
