From iris.algebra Require Import cmra proofmode_classes.
From iris.proofmode Require Import proofmode classes_make.
From iris.base_logic.lib Require Import own combine_own_classes.
From iris.prelude Require Import options.

Set Default Proof Using "Type".


(** We start with some general lemmas and [Proper] instances for constructing
  instances of the [IsValidGives], [IsValidOp], [IsIncluded] and 
  [IsIncludedOrEq] classes. *)
Section proper.
  Context {M : ucmra} {A : cmra}.
  Implicit Types a : A.

  Global Instance includedI_proper_1 : 
    NonExpansive2 (includedI (M := M) (A := A)).
  Proof. solve_proper. Qed.

  Global Instance includedI_proper_2 : 
    Proper ((≡) ==> (≡) ==> (≡)) (includedI (M := M) (A := A)).
  Proof. solve_proper. Qed.

  Global Instance is_valid_gives_proper :
    Proper ((≡) ==> (≡) ==> (=) ==> (iff)) (IsValidGives (A := A) M).
  Proof. solve_proper. Qed.

  Global Instance is_valid_op_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (iff)) (IsValidOp (A := A) M).
  Proof.
    move => a1 a1' Ha1 a2 a2' Ha2 a a' Ha.
    split; rewrite /IsValidOp.
    - rewrite -Ha -Ha2 -Ha1 //.
    - rewrite Ha2 Ha Ha1 //.
  Qed.

  Global Instance is_included_proper : 
    Proper ((≡) ==> (≡) ==> (≡) ==> (iff)) (IsIncluded (A := A) M).
  Proof. solve_proper. Qed.

  Global Instance is_included_or_eq_proper : 
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (iff)) (IsIncludedOrEq (A := A) M).
  Proof.
    move => a1 a1' Ha1 a2 a2' Ha2 P1' P1 HP1 P2' P2 HP2.
    split; case => H1 H2; split.
    - revert H1; apply is_included_proper => //.
    - rewrite -Ha2 -Ha1 -HP1 -HP2 //.
    - revert H1; apply is_included_proper => //.
    - rewrite Ha2 Ha1 HP1 HP2 //.
  Qed.


  (** The following lemma's are similar to [Proper] instances, but tailored to
    frequent usage in actual instances further on in the file. *)
  Lemma is_valid_gives_weaken a1 a2 P1 P2 :
    (✓ (a1 ⋅ a2) ∗ □ P1 ⊢ P2) →
    IsValidGives M a1 a2 P1 →
    IsValidGives M a1 a2 P2.
  Proof.
    rewrite /IsValidGives => HP1P2 HP.
    iIntros "#H✓".
    rewrite -HP1P2.
    iFrame "#". by rewrite -HP.
  Qed.

  Lemma is_valid_op_change a1 a2 a a' :
    (✓ (a1 ⋅ a2) ⊢@{uPred M} a ≡ a') →
    IsValidOp M a1 a2 a →
    IsValidOp M a1 a2 a'.
  Proof.
    rewrite /IsValidOp => Ha' Ha.
    iIntros "#H✓".
    iAssert (a ≡ a1 ⋅ a2)%I as "Ha"; first by iApply Ha.
    iAssert (a ≡ a')%I as "Ha'"; first by iApply Ha'.
    iRewrite -"Ha". by iRewrite "Ha'".
  Qed.

  Lemma is_included_weaken a1 a2 P1 P2 :
    (✓ a2 ⊢ □ P1 ∗-∗ □ P2) →
    IsIncluded M a1 a2 P1 →
    IsIncluded M a1 a2 P2.
  Proof.
    rewrite /IsIncluded => HP1P2 HP1a.
    iIntros "#H✓". iApply bi.wand_iff_trans.
    - by iApply HP1a.
    - by iApply HP1P2.
  Qed.
  Lemma is_included_or_eq_weaken a1 a2 P1 P2 P3 P4 :
    (✓ a2 ⊢ □ P1 ∗-∗ □ P3) →
    (✓ a2 ⊢ □ P2 ∗-∗ □ P4) →
    IsIncludedOrEq M a1 a2 P1 P2 →
    IsIncludedOrEq M a1 a2 P3 P4.
  Proof.
    move => HP1P3 HP2P4 [HP1 HP1P2]; split; first by eapply is_included_weaken.
    iIntros "#H✓". 
    iApply bi.wand_iff_trans; last by iApply HP2P4.
    iApply bi.wand_iff_trans; last by iApply HP1P2.
    iSplit; iIntros "[#HP|$]"; iLeft; by iApply HP1P3.
  Qed.


  (** Below instances improve proofmode support for [includedI] *)
  Global Instance includedI_into_pure `{CmraDiscrete A} (a b : A) : 
    IntoPure (PROP := uPredI M) (a ≼ b)%I (a ≼ b).
  Proof.
    rewrite /IntoPure. iDestruct 1 as (c) "%"; iPureIntro.
    by eexists.
  Qed.

  Global Instance valid_gives_emp_valid a1 a2 P:
    AsEmpValid (IsValidGives M a1 a2 P) (✓ (a1 ⋅ a2) -∗ □ P).
  Proof.
    rewrite /AsEmpValid /IsValidGives. split;
    iIntros (HP) "H✓"; by iApply HP.
  Qed.


  (** Lemma's for [IsValidGives] *)
  Lemma is_valid_gives_true a1 a2 : IsValidGives M a1 a2 True.
  Proof. rewrite /IsValidGives; eauto. Qed.


  (** Lemma's for [IsValidOp] *)
  Lemma from_isop a a1 a2 :
    IsOp a a1 a2 → IsValidOp M a1 a2 a.
  Proof. rewrite /IsOp /IsValidOp => ->; eauto. Qed.

  Lemma is_valid_gives_comm a1 a2 P :
    IsValidGives M a1 a2 P → IsValidGives M a2 a1 P.
  Proof. rewrite /IsValidGives comm //. Qed.

  Lemma is_valid_op_comm a a1 a2 :
    IsValidOp M a1 a2 a → IsValidOp M a2 a1 a.
  Proof. rewrite /IsValidOp comm => -> //. Qed.


  (** Lemma's for [IsIncluded] *)
  Lemma is_included_merge' a1 a2 P :
    IsIncluded M a1 a2 P →
    a1 ≼ a2 ⊢ ✓ a2 -∗ □ P.
  Proof.
    rewrite /IsIncluded => ->.
    iIntros "Ha1 HP".
    by iApply "HP".
  Qed.

End proper.

Global Hint Immediate is_valid_gives_true : core.


(** Next, we start giving actual instances of the classes. We start by
  providing some utility instances that should be used/can be inferred for 
  general [cmra]'s. *)
Section cmra_instances.
  Context {A : cmra} {M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  (* If [a2] has a right identity, [IsIncludedOrEq] coincides with [IsIncluded] *)
  Global Instance is_included_or_eq_from_right_id a1 a2 P :
    HasRightId a2 →
    IsIncluded M a1 a2 P →
    IsIncludedOrEq M a1 a2 P P | 100.
  Proof.
    rewrite /IsIncluded => [[e He]] HP.
    split; first done.
    rewrite HP {HP}.
    iIntros "HaP"; iSplit; last by iIntros "$".
    iIntros "[$|Ha]".
    iApply "HaP".
    iRewrite "Ha".
    by iExists _.
  Qed.

  (* If, instead, having such a right identity is contradictory, then 
    [IsIncludedOrEq] simplifies to [False] in the [≼] case.
    This instance should have higher priority than custom [IsIncludedOrEq] instances. *)
  Global Instance is_included_or_eq_id_free (a : A) :
    IdFree a →
    IsIncludedOrEq M a a False True | 5.
  Proof.
    split; last eauto 10.
    rewrite /IsIncluded; iIntros "#H✓". iSplit; last eauto.
    iDestruct 1 as "[%e #He]". iIntros "!>". (* now drop down to the model *)
    iStopProof. rewrite bi.intuitionistically_elim.
    split => n x Hx. uPred.unseal. repeat (rewrite /uPred_holds /=).
    move => [Hn Ha]. by eapply id_freeN_r.
  Qed.

  (* If no better [IsIncludedOrEq] instance is found, build it the stupid way *)
  Global Instance is_included_or_eq_last_resort a1 a2 P1 P2:
    IsIncluded M a1 a2 P1 →
    MakeOr P1 (a1 ≡ a2)%I P2 →
    IsIncludedOrEq M a1 a2 P1 P2 | 999.
  Proof.
    rewrite /MakeOr => HP1 <-.
    split; first done. 
    iIntros "_"; iSplit; iIntros "[#$|#$]".
  Qed.
End cmra_instances.


(** Similarly, we provide some simple, useful instances for general [ucmra]'s. *)
Section ucmra_instances.
  Context {A M : ucmra} (a : A).

  (** [IsValidGives] and [IsValidOp] instances for [ucmra]'s should have a
    higher cost than 5, to simplify combining with the unit element. This
    is of course not necessary if the validity simplifies to [True]. *)
  Global Instance valid_gives_unit_right :
    IsValidGives M a ε True | 5.
  Proof. eauto. Qed.
  Global Instance valid_gives_unit_left :
    IsValidGives M ε a True | 5.
  Proof. eauto. Qed.

  Global Instance valid_op_unit_right :
    IsValidOp M a ε a | 5.
  Proof. apply from_isop. rewrite /IsOp right_id //. Qed.
  Global Instance valid_op_unit_left :
    IsValidOp M ε a a | 5.
  Proof. apply is_valid_op_comm, _. Qed.

  Global Instance is_included_unit :
    IsIncluded M ε a True.
  Proof.
    rewrite /IsIncluded.
    iIntros "#H✓". iSplit; first eauto.
    iIntros "_". iExists a. by rewrite left_id.
  Qed.

  (* We do not provide an instance for [IsIncludedOrEq], instead we show
    [HasRightId] holds. The [unital_from_right_id] instance will then kick in. *)
  Global Instance has_right_id :
    HasRightId a.
  Proof. exists ε. rewrite right_id //. Qed.
End ucmra_instances.


(** Now, we provide instances for concrete [cmra]'s, starting with numbers. *)
From iris.algebra Require Import numbers frac dfrac.

Section numbers.
  Context {M : ucmra}.

  (** Instances for [natR]. This is a [ucmra], so [IsIncludedOrEq] is omitted. *)
  Global Instance nat_valid_gives (a1 a2 : nat) : IsValidGives M a1 a2 True.
  Proof. eauto. Qed.

  Global Instance nat_valid_op (a a1 a2 : nat) : 
    IsOp a a1 a2 → IsValidOp M a1 a2 a | 10.
  Proof. apply from_isop. Qed.

  Global Instance nat_is_included (a1 a2 : nat) : IsIncluded M a1 a2 ⌜a1 ≤ a2⌝.
  Proof.
    rewrite /IsIncluded.
    iIntros "_"; iSplit.
    - by iDestruct 1 as %?%nat_included.
    - iIntros "%". iExists (a2 - a1). iPureIntro.
      fold_leibniz. rewrite nat_op. lia.
  Qed.


  (** Instances for [max_natR]. This is a [ucmra], so [IsIncludedOrEq] is omitted. *)
  Global Instance max_nat_valid_gives (a1 a2 : max_nat) : 
    IsValidGives M a1 a2 True.
  Proof. eauto. Qed.

  Global Instance max_nat_valid_op (a a1 a2 : max_nat) :
    IsOp a a1 a2 → IsValidOp M a1 a2 a | 10.
  Proof. apply from_isop. Qed.

  (* We require concrete naturals here, to give the user a pretty goal. *)
  Global Instance max_nat_is_included (a1 a2 : nat) : 
    IsIncluded M (MaxNat a1) (MaxNat a2) ⌜a1 ≤ a2⌝.
  Proof.
    rewrite /IsIncluded. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%max_nat_included.
    - iIntros "%". iExists (MaxNat a2). rewrite max_nat_op.
      iPureIntro. fold_leibniz. f_equal. lia.
  Qed.


  (** Instances for [min_natR]. *)
  Global Instance min_nat_valid_gives (a1 a2 : min_nat) : 
    IsValidGives M a1 a2 True.
  Proof. eauto. Qed.

  Global Instance min_nat_valid_op (a a1 a2 : min_nat) :
    IsOp a a1 a2 → IsValidOp M a1 a2 a.
  Proof. apply from_isop. Qed.

  (* We require concrete naturals here, to give the user a pretty goal. *)
  Global Instance min_nat_is_included (a1 a2 : nat) : 
    IsIncluded M (MinNat a1) (MinNat a2) ⌜a2 ≤ a1⌝.
  Proof.
    rewrite /IsIncluded. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%min_nat_included.
    - iIntros "%". iExists (MinNat a2). rewrite min_nat_op_min. 
      iPureIntro. fold_leibniz. f_equal. lia.
  Qed.
  (* Although not a [ucmra], every [min_nat] has a right_id, which gives us
    access to the [unital_from_right_id] instance for [IsIncludedOrEq] *)
  Global Instance nat_min_has_right_id (a : min_nat) : HasRightId a.
  Proof.
    exists a. destruct a as [a'].
    rewrite min_nat_op_min. fold_leibniz. f_equal. lia.
  Qed.


  (** Instances for [positiveR]. *)
  Global Instance positive_valid_gives (a1 a2 : positive) :
    IsValidGives M a1 a2 True.
  Proof. eauto. Qed.

  Global Instance positive_valid_op (a a1 a2 : positive) :
    IsOp a a1 a2 → IsValidOp M a1 a2 a.
  Proof. apply from_isop. Qed.

  Global Instance positive_is_included (a1 a2 : positive) : 
    IsIncluded M a1 a2 ⌜(a1 < a2)%positive⌝.
  Proof. 
    rewrite /IsIncluded. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%pos_included.
    - iIntros "%". iExists (a2 - a1)%positive. iPureIntro. 
      fold_leibniz. rewrite pos_op_add. lia.
  Qed.

  Global Instance positive_is_included_or_eq (a1 a2 : positive) : 
    IsIncludedOrEq M a1 a2 ⌜(a1 < a2)%positive⌝ ⌜(a1 ≤ a2)%positive⌝ | 20.
  Proof.
    constructor; first apply _.
    iIntros "_"; iSplit.
    - iIntros "[%|->]"; eauto with lia.
    - iIntros "%H". iPureIntro. fold_leibniz. lia.
  Qed.


  (** Instances for [fracR]. *)
  Global Instance frac_valid_gives (q1 q2 : Qp) :
    IsValidGives M q1 q2 ⌜q1 + q2 ≤ 1⌝%Qp%I.
  Proof. by iDestruct 1 as %?%frac_valid. Qed.

  Global Instance frac_valid_op (q q1 q2 : Qp) :
    IsOp q q1 q2 → IsValidOp M q1 q2 q.
  Proof. apply from_isop. Qed.

  Global Instance frac_is_included (q1 q2 : Qp) : 
    IsIncluded M q1 q2 ⌜(q1 < q2)%Qp⌝.
  Proof. 
    rewrite /IsIncluded. iIntros "_" ; iSplit.
    - by iDestruct 1 as %?%frac_included.
    - iIntros "%H". apply Qp.lt_sum in H as [q' ->]. eauto.
  Qed.

  Global Instance frac_is_included_or_eq (q1 q2 : Qp) : 
    IsIncludedOrEq M q1 q2 ⌜(q1 < q2)%Qp⌝ ⌜(q1 ≤ q2)%Qp⌝ | 20.
  Proof.
    constructor; first apply _.
    iIntros "_"; iSplit.
    - iIntros "[%|->]"; eauto. iPureIntro. by apply Qp.lt_le_incl.
    - iIntros "%H".
      destruct (Qp.le_lteq q1 q2) as [[?|?] _]; eauto.
  Qed.


  (** Instance for [dfracR], for all combination of constructors.
      (Except [DfracBoth], which clients should not use? )
      - DfracOwn, DfracOwn *)
  Global Instance dfrac_own_valid_gives (q1 q2 : Qp) Pq :
    IsValidGives M q1 q2 Pq → IsValidGives M (DfracOwn q1) (DfracOwn q2) Pq.
  Proof. by rewrite /IsValidGives dfrac_validI /= frac_validI. Qed.

  Global Instance dfrac_own_valid_op (q q1 q2 : Qp) :
    IsValidOp M q1 q2 q → IsValidOp M (DfracOwn q1) (DfracOwn q2) (DfracOwn q).
  Proof.
    rewrite /IsValidOp /op /cmra_op /= dfrac_validI -frac_validI => ->.
    iIntros "->" => //.
  Qed.

  Global Instance dfrac_own_is_included (q1 q2 : Qp) Pq : 
    IsIncluded M q1 q2 Pq → 
    IsIncluded M (DfracOwn q1) (DfracOwn q2) Pq.
  Proof. 
    rewrite /IsIncluded dfrac_validI -frac_validI => ->.
    iApply bi.wand_iff_trans. iSplit.
    - iDestruct 1 as %?%dfrac_own_included. iPureIntro. by apply frac_included.
    - iDestruct 1 as %[q' ->]%frac_included%Qp.lt_sum.
      by iExists (DfracOwn q').
  Qed.

  Global Instance dfrac_own_is_included_or_eq (q1 q2 : Qp) Pq Pq' : 
    IsIncludedOrEq M q1 q2 Pq Pq' → 
    IsIncludedOrEq M (DfracOwn q1) (DfracOwn q2) Pq Pq' | 20.
  Proof.
    case => Hpq Hpq'. split; first apply _.
    rewrite dfrac_validI -frac_validI Hpq'.
    iApply bi.wand_iff_trans. iSplit.
    - iIntros "[Hpq|%H]"; eauto. iRight. case: H => -> //.
    - iIntros "[Hpq|->]"; eauto.
  Qed.

  (** - DfracOwn, DfracDiscarded *)
  Global Instance dfrac_own_discarded_valid_gives (q : Qp) :
    IsValidGives M (DfracOwn q) DfracDiscarded ⌜q < 1⌝%Qp%I.
  Proof. rewrite /IsValidGives dfrac_validI /=. eauto. Qed.

  Global Instance dfrac_discarded_own_valid_gives (q : Qp) :
    IsValidGives M DfracDiscarded (DfracOwn q) ⌜q < 1⌝%Qp%I.
  Proof. apply is_valid_gives_comm, _. Qed.

  Global Instance dfrac_own_discarded_valid_own (q : Qp) :
    IsValidOp M (DfracOwn q) DfracDiscarded (DfracOwn q ⋅ DfracDiscarded).
  Proof. rewrite /IsValidOp. eauto. Qed.

  Global Instance dfrac_discarded_own_valid_own (q : Qp) :
    IsValidOp M DfracDiscarded (DfracOwn q) (DfracOwn q ⋅ DfracDiscarded).
  Proof. apply is_valid_op_comm, _. Qed.

  Global Instance dfrac_own_discarded_is_included (q : Qp) :
    IsIncluded M (DfracOwn q) DfracDiscarded False.
  Proof.
    rewrite /IsIncluded.
    iIntros "_". iSplit => //.
    iIntros "[%dq %Hdq]". destruct dq => //=.
  Qed.

  Global Instance dfrac_discarded_own_is_included (q : Qp) :
    IsIncluded M DfracDiscarded (DfracOwn q) False.
  Proof.
    rewrite /IsIncluded.
    iIntros "_". iSplit => //.
    iIntros "[%dq %Hdq]". destruct dq => //=.
  Qed.

  (** - DfracDiscarded, DfracDiscarded *)
  Global Instance dfrac_discarded_valid_gives :
    IsValidGives M DfracDiscarded DfracDiscarded True.
  Proof. eauto. Qed.

  Global Instance dfrac_discarded_valid_op :
    IsValidOp M DfracDiscarded DfracDiscarded DfracDiscarded.
  Proof. rewrite /IsValidOp. eauto. Qed.

  Global Instance dfrac_discarded_is_included :
    IsIncluded M DfracDiscarded DfracDiscarded True.
  Proof.
    rewrite /IsIncluded.
    iIntros "_". iSplit; first eauto.
    iIntros "_". by iExists DfracDiscarded.
  Qed.

  Global Instance dfrac_discarded_right_id : HasRightId DfracDiscarded.
  Proof. exists DfracDiscarded => //. Qed.
End numbers.


(** Instances for [gsetR] and [gset_disjR]. *)
From iris.algebra Require Import gset.

Section sets.
  Context `{Countable K} {M : ucmra}.
  Implicit Types X Y Z : gset K.

  (** Instance for [gsetR]. This is a [ucmra], so [IsIncludedOrEq] is omitted. *)
  Global Instance gset_valid_gives X Y Z : IsValidGives M X Y True.
  Proof. eauto. Qed.

  Global Instance gset_valid_op X Y Z : IsOp X Y Z → IsValidOp M Y Z X | 10.
  Proof. apply from_isop. Qed.

  Global Instance gset_is_included X Y : IsIncluded M X Y ⌜X ⊆ Y⌝.
  Proof. 
    rewrite /IsIncluded. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%gset_included. 
    - iIntros "%". iExists Y. iPureIntro. set_solver.
  Qed.


  (** Instance for [gset_disjR]. This is a [ucmra], so [IsIncludedOrEq] is omitted. *)
  Global Instance gset_disj_valid_gives X Y : 
    IsValidGives M (GSet X) (GSet Y) ⌜X ## Y⌝ | 10.
  Proof. by iDestruct 1 as %?%gset_disj_valid_op. Qed.

  Global Instance gset_disj_valid_op X Y :
    IsValidOp M (GSet X) (GSet Y) (GSet (X ∪ Y)) | 10.
  Proof.
    rewrite /IsValidOp is_valid_gives.
    iDestruct 1 as %?.
    by rewrite gset_disj_union.
  Qed.

  Global Instance gset_disj_is_included X Y : 
    IsIncluded M (GSet X) (GSet Y) ⌜X ⊆ Y⌝.
  Proof. 
    rewrite /IsIncluded. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%gset_disj_included. 
    - iIntros "%".
      iExists (GSet (Y ∖ X)).
      iPureIntro. rewrite gset_disj_union; [|set_solver]. 
      f_equiv. by apply union_difference_L.
  Qed.

  (** TODO: I used to give explicit instances for combining with
     the empty set, but that does not seem necessary? *)
End sets.


(** Instances for [gmultisetR]. This is a [ucmra], so [IsIncludedOrEq] is omitted. *)
From iris.algebra Require Import gmultiset.

Section multisets.
  Context `{Countable K} {M : ucmra}.
  Implicit Types X Y Z : gmultiset K.

  Global Instance gmultiset_valid_gives X Y : IsValidGives M X Y True.
  Proof. eauto. Qed.

  Global Instance gmultiset_valid_op X Y Z :
    IsOp X Y Z → IsValidOp M Y Z X | 10.
  Proof. apply from_isop. Qed.

  Global Instance gmultiset_is_included X Y : IsIncluded M X Y ⌜X ⊆ Y⌝.
  Proof.
    rewrite /IsIncluded. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%gmultiset_included. 
    - iIntros "%". iExists (Y ∖ X). iPureIntro. fold_leibniz. rewrite gmultiset_op. multiset_solver.
  Qed.
End multisets.


(** Instances for [coPsetR] and [coPset_disjR]. *)
From iris.algebra Require Import coPset.

Section coPsets.
  Context {M : ucmra}.
  Implicit Types X Y Z : coPset.

  (** Instances for [coPsetR]. This is a [ucmra], so [IsIncludedOrEq] is omitted. *)
  Global Instance coPset_valid_gives X Y : IsValidGives M X Y True.
  Proof. eauto. Qed.

  Global Instance coPset_valid_op X Y Z :
    IsOp X Y Z → IsValidOp M Y Z X | 10.
  Proof. apply from_isop. Qed.

  Global Instance coPset_is_included X Y : IsIncluded M X Y ⌜X ⊆ Y⌝.
  Proof. 
    rewrite /IsIncluded. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%coPset_included. 
    - iIntros "%". iExists Y. iPureIntro. set_solver.
  Qed.


  (** Instances for [coPset_disjR]. This is a [ucmra], so [IsIncludedOrEq] is omitted. *)

  Global Instance coPset_disj_valid_gives X Y :
    IsValidGives M (CoPset X) (CoPset Y) ⌜X ## Y⌝ | 10.
  Proof. by iDestruct 1 as %?%coPset_disj_valid_op. Qed.

  Global Instance coPset_disj_valid_op X Y :
    IsValidOp M (CoPset X) (CoPset Y) (CoPset (X ∪ Y)) | 10.
  Proof.
    rewrite /IsValidOp is_valid_gives.
    iDestruct 1 as %?. by rewrite coPset_disj_union.
  Qed.

  Global Instance coPset_disj_is_included X Y : 
    IsIncluded M (CoPset X) (CoPset Y) ⌜X ⊆ Y⌝.
  Proof. 
    rewrite /IsIncluded. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%coPset_disj_included. 
    - iIntros "%".
      iExists (CoPset (Y ∖ X)).
      iPureIntro. rewrite coPset_disj_union; [|set_solver]. 
      f_equiv. by apply union_difference_L.
  Qed.

  (** TODO:  I used to give explicit instances for combining with
     the empty set, but that does not seem necessary? *)
End coPsets.


(** Next, we start giving instances for the [cmra] combinators. *)


Section optional.
  Context {A : cmra} {M : ucmra}.
  Implicit Types a : A.

  Global Instance option_some_valid_op a a1 a2 P :
    IsValidOp M a a1 a2 P → IsValidOp M (Some a) (Some a1) (Some a2) P.
  Proof. case => HP Ha. split; rewrite /IsValidGives -Some_op option_validI // Ha option_equivI //. Qed.
  Global Instance option_included_merge a1 a2 P1 P2 :
    IsIncludedOrEq M a1 a2 P1 P2 →
    IsIncluded M (Some a1) (Some a2) P2 | 100.
  Proof.
    rewrite /IsIncluded option_validI => [[HP1 HP2]].
    iIntros "#Ha2".
    iAssert (_)%I as "HP_le"; first by iApply (HP2 with "Ha2").
    iApply bi.wand_iff_trans; last done.
    rewrite HP1.
    iSplit.
    * iDestruct 1 as ([c|]) "Hc".
      + rewrite -Some_op option_equivI.
        iLeft. iApply "Ha2". by iExists c.
      + rewrite Some_op_opM /= option_equivI.
        iRewrite "Hc". eauto.
    * iIntros "[HP|Hr]".
      + iDestruct ("Ha2" with "HP") as "[%c Hc]". iExists (Some c).
        rewrite -Some_op. by iRewrite "Hc".
      + iRewrite "Hr". by iExists None.
  Qed.
  Global Instance option_none_excl_included_merge (ma : optionUR A) :
    IsIncluded M None ma True.
  Proof.
    rewrite /IsIncluded. iIntros "_". iSplit; first by eauto.
    iIntros "_". iExists ma. by rewrite left_id.
  Qed.
  Global Instance option_some_none_excl_included_merge a :
    IsIncluded M (Some a) None False.
  Proof.
    rewrite /IsIncluded. iIntros "_"; iSplit; last done.
    iDestruct 1 as ([c|]) "Hc"; by rewrite option_equivI.
  Qed.

End optional.


From iris.algebra Require Import csum.

Section csum.
  Context {A B : cmra} {M : ucmra}.
  Implicit Types P : uPred M.
  Implicit Types a : A.
  Implicit Types b : B.

  Global Instance sum_inl_valid_op a a1 a2 P :
    IsValidOp _ a a1 a2 P → 
    IsValidOp _ (Cinl a) (Cinl (B := B) a1) (Cinl (B := B) a2) P.
  Proof.
    case => HP Ha. 
    split; rewrite /IsValidGives -Cinl_op csum_validI // Ha.
    iIntros "Ha".
    by iRewrite "Ha".
  Qed.
  Global Instance sum_inr_valid_op b b1 b2 P :
    IsValidOp _ b b1 b2 P → 
    IsValidOp _ (Cinr b) (Cinr (A := A) b1) (Cinr (A := A) b2) P.
  Proof.
    case => HP Ha. 
    split; rewrite /IsValidGives -Cinr_op csum_validI // Ha.
    iIntros "Ha".
    by iRewrite "Ha".
  Qed.
  Global Instance sum_inl_inr_invalid_op a b :
    IsValidOp M (CsumBot) (Cinl (B := B) a) (Cinr (A := A) b) False.
  Proof. split; rewrite /IsValidGives /op /= /cmra_op /= csum_validI; eauto. Qed.
  Global Instance sum_inr_inl_invalid_op a b :
    IsValidOp M (CsumBot) (Cinr (A := B) a) (Cinl (B := A) b) False.
  Proof. split; rewrite /IsValidGives /op /= /cmra_op /= csum_validI; eauto. Qed.
  Global Instance sum_inl_included_merge a1 a2 P :
    IsIncluded _ a1 a2 P →
    IsIncluded _ (Cinl (B := B) a1) (Cinl (B := B) a2) P | 100.
  Proof.
    rewrite /IsIncluded => HaP.
    iIntros "#H✓"; iSplit.
    - iDestruct 1 as (c) "#Hc".
      rewrite csum_equivI csum_validI.
      destruct c; [ | done..].
      iApply HaP; first done.
      by iExists _.
    - rewrite csum_validI HaP.
      iIntros "#HP".
      iDestruct ("H✓" with "HP") as (c) "Hc".
      iRewrite "Hc".
      by iExists (Cinl _).
  Qed.
  Global Instance sum_inl_included_merge_unital a1 a2 P1 P2 :
    IsIncludedOrEq _ a1 a2 P1 P2 →
    IsIncludedOrEq _ (Cinl (B := B) a1) (Cinl (B := B) a2) P1 P2 | 100.
  Proof.
    case => HP_lt HP_le; split; first apply _.
    rewrite csum_validI HP_le.
    iApply bi.wand_iff_trans.
    iSplit; iIntros "[$|H]"; iRight; rewrite csum_equivI //.
  Qed.
  Global Instance sum_inr_included_merge b1 b2 P :
    IsIncluded _ b1 b2 P →
    IsIncluded _ (Cinr (A := A) b1) (Cinr (A := A) b2) P | 100.
  Proof.
    rewrite /IsIncluded => HaP.
    iIntros "#H✓"; iSplit.
    - iDestruct 1 as (c) "#Hc".
      rewrite csum_equivI csum_validI.
      destruct c; [ done| |done ].
      iApply HaP; first done.
      by iExists _.
    - rewrite csum_validI HaP.
      iIntros "#HP".
      iSpecialize ("H✓" with "HP").
      iDestruct "H✓" as (c) "Hc".
      iRewrite "Hc".
      by iExists (Cinr c).
  Qed.
  Global Instance sum_inr_included_merge_unital b1 b2 P1 P2 :
    IsIncludedOrEq _ b1 b2 P1 P2 →
    IsIncludedOrEq _ (Cinr (A := A) b1) (Cinr (A := A) b2) P1 P2 | 100.
  Proof.
    case => HP_lt HP_le; split; first apply _.
    rewrite csum_validI HP_le.
    iApply bi.wand_iff_trans.
    iSplit; iIntros "[$|H]"; iRight; rewrite csum_equivI //.
  Qed.
  Global Instance sum_inl_inr_included_merge a b :
    IsIncluded M (Cinl a) (Cinr b) False | 100.
  Proof.
    rewrite /IsIncluded; iIntros "_"; iSplit; last done.
    iDestruct 1 as ([c|c|]) "#Hc"; rewrite csum_equivI //.
  Qed.
  Global Instance sum_inr_inl_included_merge a b :
    IsIncluded M (Cinr b) (Cinl a) False | 100.
  Proof.
    rewrite /IsIncluded; iIntros "_"; iSplit; last done.
    iDestruct 1 as ([c|c|]) "#Hc"; rewrite csum_equivI //.
  Qed.
  Global Instance csum_right_id_l a :
    HasRightId a → HasRightId (Cinl (B := B) a).
  Proof. 
    move => [r rH].
    exists (Cinl r).
    rewrite -Cinl_op -rH //.
  Qed.
  Global Instance csum_right_id_r b :
    HasRightId b → HasRightId (Cinr (A := A) b).
  Proof. 
    move => [r rH].
    exists (Cinr r).
    rewrite -Cinr_op -rH //.
  Qed.

End csum.


Section prod.
  Context {X Y : cmra} {M : ucmra}.
  Implicit Types x : X.
  Implicit Types y : Y.
  Implicit Types P : uPred M.

  Global Instance prod_valid_op x x1 x2 y y1 y2 P1 P2 P :
    IsValidOp _ x x1 x2 P1 → 
    IsValidOp _ y y1 y2 P2 → 
    MakeAnd P1 P2 P →
    IsValidOp _ (x, y) (x1, y1) (x2, y2) P.
  Proof.
    rewrite /MakeAnd => Hxs Hys HP. split; rewrite /IsValidGives -pair_op prod_validI /=.
    - rewrite !is_valid_op_gives -HP bi.intuitionistically_and //.
    - rewrite prod_equivI /= !is_valid_op //.
  Qed.

  Lemma prod_includedI x1 x2 y1 y2 :
    (x1, y1) ≼ (x2, y2) ⊣⊢@{uPredI M} (x1 ≼ x2) ∧ (y1 ≼ y2).
  Proof.
    apply (anti_symm _).
    - iDestruct 1 as ([x y]) "Hc".
      rewrite -pair_op prod_equivI /=.
      iDestruct "Hc" as "[Hx Hy]"; iSplit; by iExists _.
    - iDestruct 1 as "[[%x Hx] [%y Hy]]".
      iRewrite "Hx"; iRewrite "Hy".
      by iExists (_, _).
  Qed.

  Global Instance prod_included_merge x1 x2 y1 y2 P1 P2 P :
    IsIncluded _ x1 x2 P1 →
    IsIncluded _ y1 y2 P2 →
    MakeAnd P1 P2 P →
    IsIncluded _ (x1, y1) (x2, y2) P.
  Proof.
    rewrite /IsIncluded /MakeAnd => HP1 HP2 <-.
    rewrite bi.intuitionistically_and prod_validI /=.
    rewrite prod_includedI.
    iIntros "[#Hx✓ #Hy✓]"; iSplit.
    - iDestruct 1 as "[Hz1 Hz2]".
      iSplit.
      * by iApply HP1. 
      * by iApply HP2.
    - iIntros "[#HP1 #HP2]".
      rewrite HP1 HP2.
      iSplit.
      * by iApply "Hx✓".
      * by iApply "Hy✓".
  Qed.

  (* This is the most tricky instance of the bunch. 
     The goal of this instance is to obtain good assertions for, i.e. (Some (q, p) ≼ Some (q', p')) (in the cmra: optionUR (prodR fracR positiveR))
     The naive way of doing things would give (q < q' ∧ p < p') ∨ (q = q' ∧ p = p'). We would like to get q ≤ q' and p ≤ p' directly,
      while still allowing the user to look into the disjunction if required. *)
  Global Instance prod_included_merge_unital x1 x2 y1 y2 P1_lt P1_le P2_lt P2_le P_lt P_le P_le' P_lt_case P_lt_case' P_case :
    IsIncludedOrEq M x1 x2 P1_lt P1_le → 
    IsIncludedOrEq _ y1 y2 P2_lt P2_le →
    MakeAnd P1_le P2_le P_le' →
    MakeAnd P1_lt P2_lt P_lt →
    TCIf (HasRightId x2) (TCEq P_lt_case' True%I) (TCEq P_lt_case' P1_lt) →
    TCIf (HasRightId y2) (TCEq P_lt_case P_lt_case') (MakeAnd P_lt_case' P2_lt P_lt_case) →
    MakeOr P_lt_case (x1 ≡ x2 ∧ y1 ≡ y2)%I P_case → (* MakeOr will simplify True ∨ P ⊣⊢ True and False ∨ P ⊣⊢ P *)
    MakeAnd P_le' P_case P_le →
    IsIncludedOrEq _ (x1, y1) (x2, y2) P_lt P_le.
  Proof.
    rewrite /MakeAnd /MakeOr /HasRightId => HP1 HP2 HP1P2 HP1P2' HTC1 HTC2 HPcase HPle.
    split.
    { apply: prod_included_merge.
      * apply HP1.
      * apply HP2.
      * done. }
    rewrite prod_validI /= -HPle {HPle} -HPcase {HPcase} -HP1P2 {HP1P2} -HP1P2' {HP1P2'} prod_equivI /=.
    iIntros "[#H✓x #H✓y]".
    iAssert (✓ y2 ∗ ✓ x2)%I as "[H✓y2 H✓x2]"; first by eauto.
    case: HP1 => + HP1. rewrite {1}HP1.
    case: HP2 => + HP2. rewrite {1}HP2.
    rewrite /IsIncluded => HP1' HP2'.
    iSplit.
    - iIntros "[#[Hc1 Hc2]|#[Hc1 Hc2]] !>"; iSplit; [iSplit | | iSplit | by eauto].
      + iApply bi.intuitionistically_elim. iApply "H✓x". eauto.
      + iApply bi.intuitionistically_elim. iApply "H✓y". eauto.
      + iLeft. case: HTC1; case: HTC2.
        * move => _ -> _ -> //.
        * move => <- _ ->. eauto.
        * move => _ -> -> //.
        * move => <- ->. eauto.
      + iApply bi.intuitionistically_elim. iApply "H✓x". eauto.
      + iApply bi.intuitionistically_elim. iApply "H✓y". eauto.
    - iIntros "#[[HP1_le HP2_le] [Hlt|[Hx Hy]]]"; last by iRight; iSplit.
      case: HTC1; case: HTC2.
      * move => Hy -> Hx ->.
        iDestruct ("H✓x" with "HP1_le") as "#[#$|H]".
        + iLeft.
          iDestruct ("H✓y" with "HP2_le") as "#[#$|Hy]".
          iApply (HP1' with "H✓y2"). by iRewrite "Hy".
        + iFrame "H". iDestruct ("H✓y" with "HP2_le") as "#[#$|$]".
          iLeft. iApply (HP2' with "H✓x2"). by iRewrite "H".
      * move => <- Hx ->. rewrite left_id.
        iFrame "Hlt".
        iDestruct ("H✓x" with "HP1_le") as "[#$|H]".
        iLeft.
        iApply (HP2' with "H✓x2"). by iRewrite "H".
      * move => Hy -> ->.
        iFrame "Hlt".
        iDestruct ("H✓y" with "HP2_le") as "[#$|H]".
        iLeft.
        iApply (HP1' with "H✓y2"). by iRewrite "H".
      * move => <- ->. by iLeft.
  Qed.
  Global Instance prod_right_id_both x y :
    HasRightId x → HasRightId y → HasRightId (x, y).
  Proof.
    rewrite /HasRightId.
    case => c Hx1.
    case => c' Hx2.
    exists (c, c').
    by rewrite -pair_op -Hx1 -Hx2.
  Qed.

End prod. 
(* extra instance because TC resolution gets confused for ucmras :( *)
Global Instance prod_included_merge_ucmra {X Y : ucmra} (x1 x2 : X) (y1 y2 : Y) {M} P1 P2 P :
  IsIncluded M x1 x2 P1 →
  IsIncluded M y1 y2 P2 →
  MakeAnd P1 P2 P →
  IsIncluded _ (x1, y1) (x2, y2) P.
Proof. simple eapply prod_included_merge. Qed.


From iris.algebra Require Import excl.

Section excl.
  Context {O : ofe} {M : ucmra}.
  Implicit Types o : O.
  Implicit Types e : excl O.

  Global Instance excl_valid_op e1 e2 :
    IsValidOp M ExclBot e1 e2 False.
  Proof. split; rewrite /IsValidGives excl_validI /=; eauto. Qed.
  Global Instance excl_included_merge e1 e2 :
    IsIncluded M e1 e2 False.
  Proof.
    rewrite /IsIncluded. rewrite excl_validI. destruct e2 as [o2|]; last eauto.
    iIntros "_". iSplit; last eauto. iDestruct 1 as (c) "Hc".
    rewrite /op /cmra_op /= /excl_op_instance excl_equivI //.
  Qed.
  Global Instance excl_included_merge_unital o1 o2 :
    IsIncludedOrEq M (Excl o1) (Excl o2) False (o1 ≡ o2).
  Proof.
    apply: Build_IsIncludedOrEq.
    iIntros "_"; iSplit.
    - iIntros "[[]|#H] !>". rewrite excl_equivI //.
    - iIntros "#H". iRewrite "H". eauto.
  Qed.

End excl.


From iris.algebra Require Import agree.

Section agree.
  Context {O : ofe} {M : ucmra}.
  Implicit Types o : O.

  Global Instance agree_valid_op o1 o2 :
    IsValidOp M (to_agree o1) (to_agree o1) (to_agree o2) (o1 ≡ o2)%I.
  Proof.
    split; rewrite /IsValidGives agree_validI agree_equivI; first eauto.
    iIntros "H".
    iRewrite "H".
    by rewrite agree_idemp.
  Qed.
  Global Instance agree_has_right_id o : HasRightId (to_agree o).
  Proof. exists (to_agree o). by rewrite agree_idemp. Qed.
  Lemma to_agree_op_simple (a1 a2 : agree O) o : a1 ⋅ a2 ≡ to_agree o ⊢@{uPredI M} a1 ≡ a2 ∧ a2 ≡ to_agree o.
  Proof.
    iIntros "#Heq".
    iAssert (a1 ≡ a2)%I as "#H".
    - iApply agree_validI.
      by iRewrite "Heq".
    - iFrame "H". iRewrite -"Heq". iRewrite "H". rewrite agree_idemp //.
  Qed.
  Global Instance agree_included_merge_direct o1 o2 :
    IsIncluded M (to_agree o1) (to_agree o2) (o1 ≡ o2) | 10.
  Proof.
    rewrite /IsIncluded.
    iIntros "_". iSplit. 
    - iDestruct 1 as (c) "H2". iDestruct (internal_eq_sym with "H2") as "H".
      rewrite to_agree_op_simple. iDestruct "H" as "[Heq1 Heq2]".
      iRevert "Heq1". iRewrite "Heq2".
      rewrite agree_equivI. eauto.
    - iIntros "#H". iRewrite "H". 
      iExists (to_agree o2). by rewrite agree_idemp.
  Qed.
  Global Instance agree_included_merge_abstract o1 (a : agree O) :
    IsIncluded M (to_agree o1) a (a ≡ to_agree o1) | 20.
  Proof.
    rewrite /IsIncluded.
    iIntros "H✓". iSplit. 
    - iDestruct 1 as (c) "#H2".
      iRevert "H✓".
      iRewrite "H2". iIntros "#Hoc".
      rewrite agree_validI.
      iRewrite -"Hoc". by rewrite agree_idemp.
    - iIntros "#H". iRewrite "H".
      iExists (to_agree o1). by rewrite agree_idemp.
  Qed.

End agree.


From iris.algebra Require Import gmap.

Section gmap.
  Context `{Countable K} {A : cmra} {M : ucmra}.
  Implicit Types m : gmap K A.
  Implicit Types k : K.
  Implicit Types a : A.

  (* move these to algebra/gmap? *)
  Global Instance gmap_is_op m m1 m2 :
    IsOp (merge op m1 m2) m1 m2 | 20.
  Proof. rewrite /IsOp //. Qed.
  Global Instance gmap_is_op_unit_l m :
    IsOp m m ∅ | 10.
  Proof. rewrite /IsOp right_id //. Qed.
  Global Instance gmap_is_op_unit_r m :
    IsOp m ∅ m | 10.
  Proof. rewrite /IsOp left_id //. Qed.

  Global Instance gmap_is_valid_op m m1 m2 :
    IsOp m m1 m2 → IsValidOp M m m1 m2 True | 10.
  Proof. apply from_isop. Qed.
  Global Instance gmap_included_merge m1 m2 : 
    IsIncluded M m1 m2 (∃ m, ∀ i, m2 !! i ≡ m1 !! i ⋅ m !! i) | 100.
  Proof. 
    rewrite /IsIncluded. iIntros "_"; iSplit.
    - iIntros "[%m #Hm] !>". iExists (m).
      iIntros (i). rewrite gmap_equivI -lookup_op. iApply "Hm".
    - iIntros "[%m #Hm]". iExists (m). rewrite gmap_equivI. iIntros (i). rewrite lookup_op. iApply "Hm".
  Qed.
  Global Instance gmap_included_merge_singleton m k a : 
    IsIncluded M {[ k := a ]} m (∃ a', m !! k ≡ Some a' ∧ Some a ≼ Some a' )%I | 50. (* if m !! k would reduce, we could do better *)
  Proof.
    eapply is_included_weaken; [tc_solve | ].
    iIntros "#H✓"; iSplit.
    - iIntros "[%m' #Hm] !>".
      iSpecialize ("Hm" $! k). rewrite lookup_singleton //.
      rewrite Some_op_opM.
      iExists (a ⋅? _). iFrame "Hm".
      iExists (m' !! k). rewrite Some_op_opM //.
    - iIntros "#[%a' [Hk [%ma Hma]]] !>". rewrite Some_op_opM (option_equivI (Some a')).
      destruct ma as [a''| ] => /=.
      * iExists (<[k := a'']> m). iIntros (i).
        destruct (decide (k = i)) as [-> | Hneq].
        + rewrite lookup_singleton lookup_insert. iRewrite "Hk". by iApply option_equivI.
        + rewrite lookup_singleton_ne // left_id lookup_insert_ne //.
      * iExists (delete k m). iIntros (i).
        destruct (decide (k = i)) as [-> | Hneq].
        + rewrite lookup_singleton lookup_delete // right_id. by iRewrite -"Hma".
        + rewrite lookup_singleton_ne // left_id lookup_delete_ne //.
  Qed.

End gmap.


From iris.algebra Require Import reservation_map.

Section reservation_map.
  Context {A : cmra} {M : ucmra}.
  Implicit Types a b : A.
  Implicit Types x y : reservation_map A.
  Implicit Types k : positive.
  Implicit Types P : uPred M.

  Lemma reservation_validI x : (* other direction does not hold since the disjointness criteria is not mentioned here *)
    ✓ x ⊢@{uPredI M} ✓ (reservation_map_data_proj x) ∧ ✓ (reservation_map_token_proj x).
  Proof.
    split => n y Hy. uPred.unseal => /=.
    repeat (rewrite /uPred_holds /=). rewrite reservation_map_validN_eq /=.
    destruct x as [m [E|]] => //=. 
    case; split; first done. exact I.
  Qed.

  Lemma reservation_op x y : x ⋅ y = ReservationMap (reservation_map_data_proj x ⋅ reservation_map_data_proj y) (reservation_map_token_proj x ⋅ reservation_map_token_proj y).
  Proof. done. Qed.

  Lemma reservation_equivI x y :
    x ≡ y ⊣⊢@{uPredI M} (reservation_map_data_proj x ≡ reservation_map_data_proj y) ∧ (reservation_map_token_proj x ≡ reservation_map_token_proj y).
  Proof. by uPred.unseal. Qed.

  Global Instance combine_reservation_token E1 E2 :
    IsValidOp M (reservation_map_token (A := A) (E1 ∪ E2)) (reservation_map_token E1) (reservation_map_token E2) ⌜E1 ## E2⌝.
  Proof.
    split; rewrite /IsValidGives reservation_op reservation_validI /= !is_valid_op_gives.
    - iIntros "[_ #$]".
    - iIntros "[_ %]".
      rewrite reservation_map_token_union //.
  Qed.

  Lemma reservation_map_data_validI k b :
    ✓ reservation_map_data k b ⊣⊢@{uPredI M} ✓ b.
  Proof.
    split => n. uPred.unseal => //.
    rewrite /uPred_holds /= reservation_map_validN_eq /=.
    move => x Hx.
    rewrite singleton_validN.
    split; naive_solver.
  Qed.

  Global Instance combine_reservation_data k b b1 b2 P :
    IsValidOp _ b b1 b2 P →
    IsValidOp _ (reservation_map_data k b) (reservation_map_data k b1) (reservation_map_data k b2) P.
  Proof.
    split; rewrite /IsValidGives -reservation_map_data_op reservation_map_data_validI.
    - rewrite is_valid_gives //.
    - rewrite is_valid_op.
      iIntros "Heq".
      by iRewrite "Heq".
  Qed.

  Global Instance reservation_token_included_merge E1 E2 P :
    IsIncluded _ (CoPset E1) (CoPset E2) P →
    IsIncluded _ (reservation_map_token (A := A) E1) (reservation_map_token E2) P.
  Proof.
    rewrite /IsIncluded.
    iIntros (HP) "H✓"; iSplit.
    - iDestruct 1 as ([m mE]) "#Hm". iRevert "H✓".
      iRewrite "Hm". rewrite reservation_op /= reservation_validI /= reservation_equivI /=.
      destruct mE as [E|]; iIntros "[_ %]"; last done.
      iApply HP; first done.
      iExists (CoPset E).
      iDestruct "Hm" as "[_ $]".
    - iIntros "#HP".
      iAssert (CoPset E1 ≼ CoPset E2)%I as "[%E HE]"; first by iApply HP.
      iExists (ReservationMap ∅ E).
      rewrite reservation_equivI /=. by iSplit.
  Qed.

  Global Instance reservation_data_included_merge k b1 b2 P :
    IsIncluded _ (Some b1) (Some b2) P →
    IsIncluded _ (reservation_map_data k b1) (reservation_map_data k b2) P.
  Proof.
    rewrite /IsIncluded option_validI.
    iIntros (HP) "H✓". rewrite reservation_map_data_validI HP.
    iRevert "H✓". iApply bi.wand_iff_trans. iSplit.
    - iIntros "[%m #Hm]".
      destruct m as [m mE].
      rewrite reservation_equivI /= bi.and_elim_l.
      rewrite gmap_equivI.
      iSpecialize ("Hm" $! k).
      rewrite lookup_op !lookup_singleton.
      by iExists (m !! k).
    - iIntros "[%mb Hmb]".
      destruct mb as [b|].
      * rewrite -Some_op option_equivI. iRewrite "Hmb".
        iExists (reservation_map_data k b).
        rewrite reservation_equivI /= !right_id singleton_op //.
      * rewrite right_id option_equivI. iRewrite "Hmb".
        iExists ε. by rewrite right_id.
  Qed.

End reservation_map.


From iris.algebra Require Import view.

Section view.
  Context {A : ofe} {B M : ucmra} {rel : view_rel A B}.
  Implicit Types a : A.
  Implicit Types b : B.
  Implicit Types P : uPred M.
  Implicit Types v : viewR rel.

  (* embed the view relation in the logic, so we can state and work with it without dropping down to the model *)
  Program Definition rel_holds_for a b : uPred M := UPred _ (λ n _, rel n a b) _.
  Next Obligation.
    move => /= a b n1 n2 x1 x2 Hb Hx Hn.
    eapply view_rel_mono => //.
  Qed.
  Global Instance rel_holds_for_persistent a b : Persistent (rel_holds_for a b).
  Proof. rewrite /Persistent. by uPred.unseal. Qed.
  Global Instance rel_holds_proper1 : NonExpansive2 rel_holds_for.
  Proof.
    move => n a a' Ha b b' Hb /=.
    split. rewrite /uPred_holds /= => n' x Hn Hx.
    split => Hr; eapply view_rel_mono => //=.
    - by eapply dist_le.
    - exists ε. rewrite right_id. eauto using dist_le.
    - eapply dist_le; last done. rewrite Ha //.
    - exists ε. rewrite right_id. eapply dist_le; last done. rewrite Hb //.
  Qed.
  Global Instance rel_holds_proper2 : Proper ((≡) ==> (≡) ==> (⊣⊢)) rel_holds_for.
  Proof. 
    move => a a' Ha b b' Hb /=.
    split. rewrite /uPred_holds /= => n' x Hx. rewrite Ha Hb //.
  Qed.

  Lemma view_validI v :
    ✓ v ⊣⊢@{uPredI M} match view_auth_proj v with
          | Some (dq, a) =>
            ∃ a', a ≡ to_agree a' ∧ v ≡ ●V{dq} a' ⋅ ◯V (view_frag_proj v) ∧ rel_holds_for a' (view_frag_proj v) ∧ ✓ dq
          | None => v ≡ ◯V (view_frag_proj v) ∧ ∃ a, rel_holds_for a (view_frag_proj v)
          end.
  Proof.
    destruct v as [[[dq a]|] b] => /=.
    - uPred.unseal.
      split=> n y Hy.
      rewrite /upred.uPred_cmra_valid_def /= /validN /cmra_validN /= /view_validN_instance /=.
      split.
      * case => Hdq [a' [Ha1 Ha2]].
        repeat (rewrite /uPred_holds /=).
        exists a'.
        split; first done.
        split; last done.
        rewrite Ha1 /op /cmra_op /= /view_op_instance /= right_id left_id //.
      * repeat (rewrite /uPred_holds /=). naive_solver.
    - uPred.unseal. split => n y Hy //=.
      repeat (rewrite /uPred_holds /=). naive_solver.
  Qed.

  Lemma view_equivI v1 v2 :
    v1 ≡ v2 ⊣⊢@{uPredI M} view_auth_proj v1 ≡ view_auth_proj v2 ∧ view_frag_proj v1 ≡ view_frag_proj v2.
  Proof. by uPred.unseal. Qed.

  Global Instance view_frag_valid_op b b1 b2 P :
    IsOp b b1 b2 → (* generic views do not require the fragment to be valid! So this will usually not be enough *)
    IsValidOp M (view_frag (rel := rel) b) (◯V b1) (◯V b2) (∃ a, rel_holds_for a b).
  Proof.
    rewrite /IsOp => Hb; split.
    - rewrite /IsValidGives -view_frag_op view_validI /=.
      iDestruct 1 as "[_ [%a #Ha]]". rewrite -Hb. eauto.
    - rewrite Hb view_frag_op. eauto.
  Qed.

  Lemma view_auth_dfrac_op_validI dq1 dq2 a1 a2 : ✓ (view_auth (rel := rel) dq1 a1 ⋅ ●V{dq2} a2) ⊣⊢@{uPredI M} ✓ (dq1 ⋅ dq2) ∧ (a1 ≡ a2) ∧ rel_holds_for a2 ε.
  Proof.
    apply (anti_symm _); last first.
    - iIntros "(% & Ha & Hrel)".
      iRewrite "Ha".
      rewrite view_validI /=.
      iExists a2.
      rewrite agree_idemp -view_auth_dfrac_op !right_id.
      iSplit; first done.
      iSplit; last eauto.
      rewrite {2}/op /= /cmra_op /= /view_op_instance /= !right_id //.
    - rewrite view_validI /=.
      iDestruct 1 as (a) "Ha". rewrite to_agree_op_simple !agree_equivI /= right_id.
      iDestruct "Ha" as "([$ #Heq] & _ & H & $)".
      iRewrite "Heq". eauto.
  Qed.

  Global Instance view_auth_dfrac_own_valid_op a1 a2 dq dq1 dq2 Pq :
    IsValidOp M dq dq1 dq2 Pq →
    IsValidOp M (view_auth (rel := rel) dq a1) (●V{dq1} a1) (●V{dq2} a2) (Pq ∧ a1 ≡ a2 ∧ rel_holds_for a2 ε)%I.
  Proof.
    move => Hq; split.
    - rewrite /IsValidGives view_auth_dfrac_op_validI is_valid_gives.
      iIntros "(#$ & #$ & #$)".
    - rewrite view_auth_dfrac_op_validI is_valid_op.
      iIntros "(-> & Heq & _)".
      iRewrite "Heq".
      rewrite -view_auth_dfrac_op //.
  Qed.
  (* it is possible to add IncludedMerge classes for views, but that would probably be painful, and only relevant
     for the case where ●V appears nested under another ●. I think usually better ways should exist? *)  

End view.

Global Arguments rel_holds_for {A B M} rel _ _.


From iris.algebra Require Import auth.

Section auth.
  Context {A M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  Global Instance auth_frag_valid_op a a1 a2 P :
    IsValidOp M a a1 a2 P →
    IsValidOp M (◯ a) (◯ a1) (◯ a2) P.
  Proof.
    move => HPa. split; rewrite /IsValidGives -auth_frag_op auth_frag_validI //.
    - rewrite is_valid_gives //.
    - rewrite is_valid_op.
      iIntros "H".
      by iRewrite "H".
  Qed.
  Lemma auth_rel_holds a1 a2 : rel_holds_for auth_view_rel a1 a2 ⊣⊢@{uPredI M} a2 ≼ a1 ∧ ✓ a1.
  Proof. rewrite /includedI. by uPred.unseal. Qed.
  Lemma auth_auth_dfrac_op_validI dq1 dq2 a1 a2 : ✓ (●{dq1} a1 ⋅ ●{dq2} a2) ⊣⊢@{uPredI M} ✓ (dq1 ⋅ dq2) ∧ ✓ a2 ∧ (a1 ≡ a2).
  Proof.
    rewrite view_auth_dfrac_op_validI auth_rel_holds.
    eapply (anti_symm _); eauto with iFrame.
    - iIntros "($ & $ & _ & $)".
    - iIntros "($ & $ & $)". iExists a2. by rewrite left_id.
  Qed.
  Global Instance auth_auth_dfrac_own_valid_op a1 a2 dq dq1 dq2 Pq :
    IsValidOp M dq dq1 dq2 Pq →
    IsValidOp M (●{dq} a1) (●{dq1} a1) (●{dq2} a2) (Pq ∧ a1 ≡ a2).
  Proof.
    move => Hq. eapply is_valid_op_weaken. 
    - rewrite /auth_auth. tc_solve. 
    - iIntros "[_ #($ & $ & _)]".
  Qed.

  (* We do not provide IsValidOp for combinations of ● and ◯: instead, we provide IsValidGives *)
  Global Instance auth_frag_is_valid_gives dq a1 a2 P :
    IsIncluded M a2 a1 P →
    IsValidGives _ (●{dq} a1) (◯ a2) P.
  Proof.
    rewrite /IsIncluded /IsValidGives auth_both_dfrac_validI => HP.
    iIntros "(% & #Hle & #Ha)".
    by iApply HP.
  Qed.
  Global Instance auth_frag_is_valid_gives_swap dq a1 a2 P :
    IsIncluded M a2 a1 P →
    IsValidGives _ (◯ a2) (●{dq} a1) P.
  Proof. intros; eapply is_valid_gives_comm, _. Qed.
End auth.


From iris.algebra.lib Require Import frac_auth.

Section frac_auth.
  Context {A : cmra} {M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  (* overcomes the typeclasses opaque instance on frac_auth_frag *)
  Global Instance frac_auth_frag_valid_op a a1 a2 (q q1 q2 : Qp) P1 P2 :
    IsValidOp M q q1 q2 P1 →
    IsValidOp M a a1 a2 P2 →
    IsValidOp M (◯F{q} a) (◯F{q1} a1) (◯F{q2} a2) (P1 ∧ P2).
  Proof.
    intros.
    apply auth_frag_valid_op, option_some_valid_op.
    by eapply prod_valid_op.
  Qed.

  Global Instance frac_auth_frag_is_valid_gives q a1 a2 P :
    IsIncluded M (Some (q, a2)) (Some (1%Qp, a1)) P →
    IsValidGives _ (●F a1) (◯F{q} a2) P.
  Proof. eapply auth_frag_is_valid_gives. Qed.
  Global Instance frac_auth_frag_is_valid_gives_swap q a1 a2 P :
    IsIncluded M (Some (q, a2)) (Some (1%Qp, a1)) P →
    IsValidGives _ (◯F{q} a2) (●F a1) P.
  Proof. intros; eapply is_valid_gives_comm, _. Qed.
End frac_auth.


From iris.algebra.lib Require Import excl_auth.

Section excl_auth.
  Context {A : ofe} {M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  (* overcomes the typeclasses opaque instance on excl_auth_frag *)
  Global Instance excl_auth_frag_valid_op ea a1 a2 P :
    IsValidOp M (Some ea) (Excl' a1) (Excl' a2) P →
    IsValidOp M (◯ (Some ea)) (◯E a1) (◯E a2) P.
  Proof. apply auth_frag_valid_op. Qed.

  Global Instance excl_auth_frag_is_valid_gives a1 a2 P :
    IsIncluded M (Excl' a2) (Excl' a1) P →
    IsValidGives _ (●E a1) (◯E a2) P.
  Proof. eapply auth_frag_is_valid_gives. Qed.
  Global Instance excl_auth_frag_is_valid_gives_swap a1 a2 P :
    IsIncluded M (Excl' a2) (Excl' a1) P →
    IsValidGives _ (◯E a2) (●E a1) P.
  Proof. intros; eapply is_valid_gives_comm, _. Qed.
End excl_auth.


From iris.algebra.lib Require Import dfrac_agree.

Section dfrac_agree.
  Context {A : ofe} {M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  (* overcomes the typeclasses opaque instance on to_dfrac_agree *)

  Global Instance dfrac_agree_valid_op q a q1 a1 q2 a2 P :
    IsValidOp M (q, to_agree a) (q1, to_agree a1) (q2, to_agree a2) P →
    IsValidOp M (to_dfrac_agree q a) (to_dfrac_agree q1 a1) (to_dfrac_agree q2 a2) P.
  Proof. by rewrite /to_dfrac_agree. Qed.

  Global Instance dfrac_agree_included q1 a1 q2 a2 P :
    IsIncluded M (q1, to_agree a1) (q2, to_agree a2) P →
    IsIncluded M (to_dfrac_agree q1 a1) (to_dfrac_agree q2 a2) P.
  Proof. by rewrite /to_dfrac_agree. Qed.

  Global Instance dfrac_agree_included_or_eq q1 a1 q2 a2 P1 P2 :
    IsIncludedOrEq M (q1, to_agree a1) (q2, to_agree a2) P1 P2 →
    IsIncludedOrEq M (to_dfrac_agree q1 a1) (to_dfrac_agree q2 a2) P1 P2.
  Proof. by rewrite /to_dfrac_agree. Qed.

End dfrac_agree.


From iris.algebra.lib Require Import gmap_view.

Section gmap_view.
  Context {K : Type} `{Countable K} {V : ofe} {M : ucmra}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dq : dfrac) (v : V).
  Implicit Types P : uPred M.

  Lemma gmap_view_rel_holds (m : gmap K V) (f : gmap K (dfrac * agree V)) : 
    rel_holds_for (gmap_view.gmap_view_rel K V) m f ⊣⊢@{uPredI M} ∀ (i : K) dq a, ⌜f !! i = Some (dq, a)⌝ → ∃ a', a ≡ to_agree a' ∧ ✓ dq ∧ ⌜m !! i = Some a'⌝.
  Proof. 
    split => n x Hx. rewrite /includedI. uPred.unseal.
    repeat (rewrite /uPred_holds /=).
    rewrite /gmap_view.gmap_view_rel_raw /=. split.
    - move => /map_Forall_lookup Hm k dq a n' x' Hx' Hn Hx'' /Hm /= => [[v [Hv1 [Hv2 Hv3]]]].
      exists v. rewrite Hv3. split; eauto using dist_le'.
    - move => H0. apply map_Forall_lookup => k [dq a] /= /H0 {H0} H0'.
      destruct (H0' n x) as [v Hv]; eauto.
  Qed.

  Lemma gmap_view_rel_holds_singleton k dv m :
    rel_holds_for (gmap_view.gmap_view_rel K V) m {[ k := dv ]} ⊣⊢@{uPredI M} ∃ a', dv.2 ≡ to_agree a' ∧ ✓ dv.1 ∧ ⌜m !! k = Some a'⌝.
  Proof.
    rewrite gmap_view_rel_holds.
    apply (anti_symm _).
    - iIntros "Hm". destruct dv as [dq av] => /=.
      iApply ("Hm" $! k dq av). rewrite lookup_singleton //.
    - iDestruct 1 as "[%a (Ha1 & Ha2 & %Hka)]".
      iIntros (i). destruct (decide (k = i)) as [->|Hneq].
      * rewrite lookup_singleton /= Hka {Hka i}.
        iIntros (dq av Hdq). case: Hdq => -> /=.
        iExists _. eauto. 
      * rewrite lookup_singleton_ne //.
  Qed.

  Global Instance gmap_view_frag_valid_op k dq dq1 dq2 v1 v2 P :
    IsValidOp _ dq dq1 dq2 P →
    IsValidOp _ (gmap_view_frag k dq v1) (gmap_view_frag k dq1 v1) (gmap_view_frag k dq2 v2) (P ∧ v1 ≡ v2).
  Proof.
    move => H0; split.
    - rewrite /IsValidGives view_validI /=.
      iDestruct 1 as "[_ [%m Hm]]".
      rewrite singleton_op -pair_op gmap_view_rel_holds_singleton /=.
      iDestruct "Hm" as "[%v3 (#Hv3 & Hv3' & _)]".
      rewrite to_agree_op_simple is_valid_gives bi.and_elim_l agree_equivI bi.intuitionistically_and.
      eauto.
    - rewrite view_validI /=.
      iDestruct 1 as "[_ [%m Hm]]".
      rewrite singleton_op -pair_op gmap_view_rel_holds_singleton /=.
      iDestruct "Hm" as "[%v3 (Hv3 & Hv3' & _)]".
      rewrite to_agree_op_simple is_valid_op bi.and_elim_l agree_equivI.
      iRewrite "Hv3". iRewrite "Hv3'". rewrite -gmap_view_frag_op //.
  Qed.

  Global Instance gmap_view_auth_valid_op dq dq1 dq2 P m1 m2 :
    IsValidOp _ dq dq1 dq2 P →
    IsValidOp _ (gmap_view_auth dq m1) (gmap_view_auth dq1 m1) (gmap_view_auth dq2 m2) (P ∧ m1 ≡ m2).
  Proof.
    intros. eapply is_valid_op_weaken.
    - rewrite /gmap_view_auth. tc_solve.
    - iIntros "(_ & #$ & #$ & _ )".
  Qed.

  Global Instance gmap_view_auth_frag_gives dq1 m k dq2 v :
    IsValidGives M (gmap_view_auth dq1 m) (gmap_view_frag k dq2 v) (m !! k ≡ Some v).
  Proof.
    rewrite /IsValidGives view_validI /=.
    iDestruct 1 as (m') "(Hm' & _ & Hr & _)".
    iRevert "Hr". rewrite agree_equivI. iRewrite -"Hm'". clear m'.
    rewrite left_id gmap_view_rel_holds_singleton.
    iDestruct 1 as (v') "(Hv1 & Hv2 & ->)". simpl.
    rewrite agree_equivI. by iRewrite "Hv1".
  Qed.
End gmap_view.

