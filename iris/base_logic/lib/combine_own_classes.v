From iris.algebra Require Import cmra.
From iris.base_logic Require Import own.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Export cmra.
From iris.prelude Require Import options.


(* Given two valid ghost elements [a1] and [a2], [IsValidGives _ a1 a2 P]
  computes a simplified proposition [P] that follows from the validity of 
  [a1] and [a2] *)
Class IsValidGives {A : cmra} M (a1 a2 : A) (P : uPred M) :=
  is_valid_gives : ✓ (a1 ⋅ a2) ⊢ □ P.

Global Hint Mode IsValidGives ! ! ! ! - : typeclass_instances.


(* Often we can simplify [a1 ⋅ a2] to some new element [a]. This may itself
  make use of validity, for example in the case of [GSet]. The class
  [IsValidOp _ a a1 a2] says that if [a1 ⋅ a2] is valid, then [a] is a
  simplified element equivalent to [a1 ⋅ a2]. *)
Class IsValidOp {A : cmra} M (a1 a2 : A) (a : A) := 
  is_valid_op : ✓ (a1 ⋅ a2) ⊢@{uPredI M} a ≡ a1 ⋅ a2
.

Global Hint Mode IsValidOp ! ! ! ! - : typeclass_instances.


(* We can now use [IsValidGives] and [IsValidOp] to compute appropriate 'as' 
  and 'gives' clauses for [iCombine]. The cost of these instances is made
  lower than that of the fallback instances [combine_sep_as_own] and
  [combine_sep_gives_own] from [iris/base_logic/own.v]. *)
Global Instance combine_sep_from_valid_gives `{!inG Σ A} (a1 a2 a : A) γ :
  IsValidOp (iResUR Σ) a1 a2 a →
  CombineSepAs (own γ a1) (own γ a2) (own γ a) | 50.
Proof.
  rewrite /IsValidOp /CombineSepAs => Ha.
  iIntros "[Hγ1 Hγ2]".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "#H✓".
  rewrite Ha.
  iRewrite "H✓".
  by iSplitL "Hγ1".
Qed.

Global Instance combine_sep_gives_from_valid_op `{!inG Σ A} (a1 a2 : A) P γ :
  IsValidGives (iResUR Σ) a1 a2 P →
  CombineSepGives (own γ a1) (own γ a2) P | 50.
Proof.
  rewrite /CombineSepGives /IsValidGives => HP.
  iIntros "[Hγ1 Hγ2]".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "#H✓".
  by rewrite HP.
Qed.


(* We are often interested in the consequences of [✓ (● a2 ⋅ ◯ a1) ⊣⊢ a1 ≼ a2].
  We also provide additional simplification machinery for this resource.
  [IsIncluded _ a1 a2 P] computes a simplified proposition [P],
  which is equivalent to [a1 ≼ a2] if we assume [✓ a2].
  All we really need is that [P] follows from [a1 ≼ a2], but we use
  equivalence to ensure we are accidentally using weakening. *)

Class IsIncluded {A : cmra} M (a1 a2 : A) (P : uPred M) := 
  is_included_merge : ✓ a2 ⊢ a1 ≼ a2 ∗-∗ □ P.

Global Hint Mode IsIncluded ! ! ! ! - : typeclass_instances.

(* [IsIncludedOrEq] is used as a stepping stone to compute good
   [IsIncluded] instances for unital extensions of non-unital cmra's.
   Note that the [P_le] argument often has a simpler shape than [P_lt ∨ _ ≡ _]:
   Consider, for example [A := optionUR fracR]. There, we can simplify
   [q1 < q2 ∨ q1 ≡ q2] to the simpler [q1 ≤ q2]. For [cmra]'s like 
   [optionUR $ prodR fracR positiveR], it becomes a bit more difficult.
   We include [IsIncluded] for efficiency's sake, to avoid computing it twice. *)
Class IsIncludedOrEq {A : cmra} M (a1 a2 : A) (P_lt P_le : uPred M) := {
  is_included_or_included : IsIncluded M a1 a2 P_lt;
  is_included_or_eq_merge : ✓ a2 ⊢ (□ P_lt ∨ a1 ≡ a2) ∗-∗ □ P_le;
}.

Global Hint Mode IsIncludedOrEq ! ! ! ! - - : typeclass_instances.

(* [HasRightId] is also used to compute good IsIncluded instances.
   Note that this is weaker than having a unit! Consider [min_natR], [agreeR] *)
Class HasRightId {A : cmra} (a : A) :=
  has_right_id : a ≼ a.

Global Hint Mode HasRightId ! ! : typeclass_instances.





