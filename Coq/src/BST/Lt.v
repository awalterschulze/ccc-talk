Require Import ConstructionToolbox.

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