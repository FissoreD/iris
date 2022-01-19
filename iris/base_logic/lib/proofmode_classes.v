From iris.algebra Require Import cmra.
From iris.base_logic Require Import own.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.


(* Given two valid ghost elements a1 and a2, IsValidGives _ a1 a2 P computes 
  a simplified proposition P that follows from the validity of a1 and a2 *)
Class IsValidGives {A : cmra} M (a1 a2 : A) (P : uPred M) :=
  is_valid_gives : ✓ (a1 ⋅ a2) ⊢ □ P.

Global Hint Mode IsValidGives ! ! ! ! - : typeclass_instances.


(* Often we can simplify a1 ⋅ a2 to some new element a. This may make use
  of validity, for example in the case of GSet. IsValidOp _ a a1 a2 P
  says that a is a simplified element equivalent to a1 ⋅ a2, and P 
  a simplified proposition following from the validity of a1 and a2 *)
Class IsValidOp {A : cmra} M (a a1 a2 : A) (P : uPred M) := {
  is_valid_op_gives :> IsValidGives _ a1 a2 P ;
  is_valid_op : ✓ (a1 ⋅ a2) ⊢@{uPredI M} a ≡ a1 ⋅ a2 ;
}.

Global Hint Mode IsValidOp ! ! - ! ! - : typeclass_instances.


(* We are often interested in the consequences of ✓ (● _ ⋅ ◯ _).
   We do not usually want to combine these elements, which is why we have
   separated IsValidOp and IsValidGives. 
   The consequence of ✓{n} (● a ⋅ ◯ b) in the model is that b ≼{n} a ∧ ✓{n} a. 
   To cleanly reason about this in the logic, we provide notation for
   the lifted version of ≼{n} *)

Definition includedI {M : ucmra} {A : cmra} (a b : A) : uPred M
  := (∃ c, b ≡ a ⋅ c)%I.

Notation "a ≼ b" := (includedI a b) : bi_scope.


(* IsIncluded _ a1 a2 P computes a simplified proposition P,
   which is equivalent to a1 ≼ a2 if we assume ✓ a2. 
   All we need is that P follows from a1 ≼ a2, but we use 
   equivalence to ensure we are not forgetting any consequence *)

Class IsIncluded {A : cmra} M (a1 a2 : A) (P : uPred M) := 
  is_included_merge : ✓ a2 ⊢ a1 ≼ a2 ∗-∗ □ P.

Global Hint Mode IsIncluded ! ! ! ! - : typeclass_instances.

(* IsIncludedOrEq is used as a stepping stone to compute good
   IsIncluded instances for unital extensions of non-unital cmra's.
   For example, consider optionUR $ prodR fracR positiveR .
   It includes IsIncludedM for efficiency's sake, to avoid computing it twice. *)
Class IsIncludedOrEq {A : cmra} M (a1 a2 : A) (P_lt P_le : uPred M) := {
  is_included_or_included : IsIncluded M a1 a2 P_lt;
  is_included_or_eq_merge : ✓ a2 ⊢ (□ P_lt ∨ a1 ≡ a2) ∗-∗ □ P_le;
}.

Global Hint Mode IsIncludedOrEq ! ! ! ! - - : typeclass_instances.

(* HasRightId a is also used to compute good IsIncluded instances.
   Note that this is weaker than having a unit! Consider min_natR, agreeR *)
Class HasRightId {A : cmra} (a : A) :=
  has_right_id : a ≼ a.

Global Hint Mode HasRightId ! ! : typeclass_instances.