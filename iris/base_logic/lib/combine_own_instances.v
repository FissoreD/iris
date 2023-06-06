From iris.algebra Require Import cmra proofmode_classes csum excl agree.
From iris.proofmode Require Import proofmode classes_make.
From iris.base_logic.lib Require Import own combine_own_classes.
From iris.prelude Require Import options.

Set Default Proof Using "Type".


(** We start with some general lemmas and [Proper] instances for constructing
  instances of the [IsValidGives], [IsValidOp], [IsIncluded] and 
  [IsIncludedOrEq] classes. *)

Global Opaque internal_included.

Section included_extra.
  Context `{!BiInternalEq PROP}.
  Implicit Type A B : cmra.

  Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
  Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).

  Global Instance into_exist_internal_included {A} (a b : A) :
    IntoExist (PROP := PROP) (a ≼ b) (λ c, b ≡ a ⋅ c)%I (λ x, x).
  Proof. by rewrite /IntoExist. Qed.

  Global Instance from_exist_internal_included {A} (a b : A) :
    FromExist (PROP := PROP) (a ≼ b) (λ c, b ≡ a ⋅ c)%I.
  Proof. by rewrite /FromExist. Qed.

  Global Instance internal_included_persistent {A} (a b : A) : 
    Persistent (PROP := PROP) (a ≼ b).
  Proof. rewrite /Persistent. iIntros "[%c #Hc] !>". by iExists _. Qed.

  Global Instance internal_included_absorbing {A} (a b : A) : 
    Absorbing (PROP := PROP) (a ≼ b).
  Proof. rewrite /Absorbing. iIntros "[%c Hc]". iExists _. by iApply absorbing. Qed.

  Lemma internal_included_def {A} (a b : A) : a ≼ b ⊣⊢ (∃ c, b ≡ a ⋅ c).
  Proof. apply (anti_symm _); iIntros "[%c Hc]"; by iExists _. Qed.


  Lemma csum_equivI_eq {A B} (sx sy : csum A B) :
    sx ≡ sy ⊣⊢
              match sx, sy with
               | Cinl x, Cinl y => x ≡ y
               | Cinr x, Cinr y => x ≡ y
               | CsumBot, CsumBot => True
               | _, _ => False
               end.
  Proof.
    apply (anti_symm _).
    - apply (internal_eq_rewrite' sx sy (λ sy',
               match sx, sy' with
               | Cinl x, Cinl y => x ≡ y
               | Cinr x, Cinr y => x ≡ y
               | CsumBot, CsumBot => True
               | _, _ => False
               end)%I); [solve_proper|auto|].
      destruct sx; eauto.
    - destruct sx; destruct sy; eauto;
      iIntros "H"; by iRewrite "H".
  Qed.

  Lemma csum_includedI {A B} (sx sy : csum A B) :
    sx ≼ sy ⊣⊢ match sx, sy with
               | Cinl x, Cinl y => (x ≼ y)
               | Cinr x, Cinr y => (x ≼ y)
               | _, CsumBot => True
               | _, _ => False
               end.
  Proof.
    destruct sx as [x|x|]; destruct sy as [y|y|].
    - apply (anti_symm _); iIntros "[%c Hc]".
      * rewrite csum_equivI_eq. destruct c; [|done..]. by iExists _.
      * iRewrite "Hc". by iExists (Cinl c).
    - apply (anti_symm _); last eauto.
      iIntros "[%c Hc]". rewrite csum_equivI_eq. by destruct c.
    - apply (anti_symm _); first eauto. iIntros "_". by iExists CsumBot.
    - apply (anti_symm _); last eauto.
      iIntros "[%c Hc]". rewrite csum_equivI_eq. by destruct c.
    - apply (anti_symm _); iIntros "[%c Hc]".
      * rewrite csum_equivI_eq. destruct c; [done| |done]. by iExists _.
      * iRewrite "Hc". by iExists (Cinr c).
    - apply (anti_symm _); first eauto. iIntros "_". by iExists CsumBot.
    - apply (anti_symm _); last eauto.
      iIntros "[%c Hc]". rewrite csum_equivI_eq. by destruct c.
    - apply (anti_symm _); last eauto.
      iIntros "[%c Hc]". rewrite csum_equivI_eq. by destruct c.
    - apply (anti_symm _); first eauto. iIntros "_". by iExists CsumBot.
  Qed.

  Lemma excl_equivI {O : ofe} (x y : excl O) :
    x ≡ y ⊣⊢ match x, y with
             | Excl a, Excl b => a ≡ b
             | ExclBot, ExclBot => True
             | _, _ => False
             end.
  Proof.
    apply (anti_symm _).
    - apply (internal_eq_rewrite' x y (λ y',
               match x, y' with
               | Excl a, Excl b => a ≡ b
               | ExclBot, ExclBot => True
               | _, _ => False
               end)%I); [solve_proper|auto|].
      destruct x; eauto.
    - destruct x as [e1|]; destruct y as [e2|]; [|by eauto..].
      iIntros "H"; by iRewrite "H".
  Qed.

  Lemma excl_includedI {O : ofe} (x y : excl O) :
    x ≼ y ⊣⊢ match x, y with
             | _, ExclBot => True
             | _, _ => False
             end.
  Proof.
    apply (anti_symm _).
    - iIntros "[%z Hz]". iStopProof.
      apply (internal_eq_rewrite' (x ⋅ z) y (λ y',
               match x, y' with
             | _, ExclBot => True
             | _, _ => False
             end)%I); [solve_proper|apply internal_eq_sym|].
      iIntros "Hz". by destruct x; destruct z.
    - destruct y; first eauto.
      iPureIntro => _. exists ExclBot. by destruct x.
  Qed.

  Lemma agree_includedI {O : ofe} (x y : agree O) : x ≼ y ⊣⊢ y ≡ x ⋅ y.
  Proof.
    apply (anti_symm _); last (iIntros "H"; by iExists _).
    iIntros "[%c Hc]".
    iRewrite "Hc". rewrite assoc. by rewrite agree_idemp.
  Qed.
End included_extra.

(* Not a hint immediate due to unification problems of cmra <-> ucmra *)
Global Hint Extern 0 (ε ≼ _) => apply ucmra_unit_least : core.


Section included_upred.
  Context {M : ucmra}.
  Implicit Type A : cmra.
  Notation "P ⊢ Q" := (P ⊢@{uPredI M} Q).
  Notation "P ⊣⊢ Q" := (P ⊣⊢@{uPredI M} Q).

  Lemma internal_included_id_free {A} (a : A) `{!IdFree a} : a ≼ a ∗ ✓ a ⊢ False.
  Proof.
    iIntros "[[%c Hc] Hv]". iStopProof. rewrite bi.sep_and.
    split => n x Hx. uPred.unseal. repeat rewrite /uPred_holds /=.
    move => [He Hv]. by eapply id_freeN_r.
  Qed.
End included_upred.


Section proper.
  Context {M : ucmra} {A : cmra}.
  Implicit Types a : A.

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


  (** The following lemmas are similar to [Proper] instances, but tailored to
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
    (✓ (a1 ⋅ a2) ⊢@{uPredI M} a ≡ a') →
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


  (** Below instances improve proofmode support. *)
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
    rewrite /IsIncluded /HasRightId => Ha2 HP.
    split; first done.
    rewrite HP {HP}.
    iIntros "HaP"; iSplit; last by iIntros "$".
    iIntros "[$|Ha]".
    iApply "HaP". iRewrite "Ha". eauto.
  Qed.

  (* If, instead, having such a right identity is contradictory, then 
    [IsIncludedOrEq] simplifies to [False] in the [≼] case.
    This instance should have lower cost than custom [IsIncludedOrEq] instances. *)
  Global Instance is_included_or_eq_id_free (a : A) :
    IdFree a →
    IsIncludedOrEq M a a False True | 5.
  Proof.
    split; last eauto 10.
    rewrite /IsIncluded; iIntros "#H✓". iSplit; last eauto.
    iIntros "H≼".
    iDestruct (internal_included_id_free with "[$]") as "[]".
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
  Proof. rewrite /IsIncluded. eauto. Qed.

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
    - iIntros (H). iPureIntro. by apply nat_included.
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
    - iIntros (H). iPureIntro. by apply max_nat_included.
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
    - iIntros (H). iPureIntro. by apply min_nat_included.
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
    - iIntros (H). iPureIntro. by apply pos_included.
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
    - iIntros (H). iPureIntro. by apply frac_included.
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
    - iIntros (H%frac_included). iPureIntro. by apply dfrac_own_included.
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
  Proof. rewrite /IsValidGives. by iIntros (H%dfrac_valid_own_l). Qed.

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
    iIntros "_". iSplit; last done.
    iIntros "[%dq %Hdq]". by destruct dq.
  Qed.

  Global Instance dfrac_discarded_own_is_included (q : Qp) :
    IsIncluded M DfracDiscarded (DfracOwn q) False.
  Proof.
    rewrite /IsIncluded.
    iIntros "_". iSplit; last done.
    iIntros "[%dq %Hdq]". by destruct dq.
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
    - iIntros (H). iPureIntro. by apply gset_included.
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
    - iIntros (H). iPureIntro. by apply gset_disj_included.
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
    - iIntros (H). iPureIntro. by apply gmultiset_included.
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
    - iIntros (H). iPureIntro. by apply coPset_included.
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
    - iIntros (H). iPureIntro. by apply coPset_disj_included.
  Qed.

  (** TODO:  I used to give explicit instances for combining with
     the empty set, but that does not seem necessary? *)
End coPsets.


(** Next, we start giving instances for the [cmra] combinators. *)


(** Instances for [optionR]. This is a [ucmra], so [IsIncludedOrEq] is omitted. *)

Section optional.
  Context {A : cmra} {M : ucmra}.
  Implicit Types a : A.

  (** We can omit combinations with [None], since [None = ε] *)
  Global Instance option_some_valid_gives a1 a2 P :
    IsValidGives M a1 a2 P → IsValidGives M (Some a1) (Some a2) P.
  Proof. by rewrite /IsValidGives option_validI => <-. Qed.

  Global Instance option_some_valid_op a a1 a2 :
    IsValidOp M a1 a2 a → IsValidOp M (Some a1) (Some a2) (Some a).
  Proof. by rewrite /IsValidOp -Some_op option_validI option_equivI => ->. Qed.

  (** This instance is the main reason for the [IsIncludedOrEq] typeclass:
     so that we precompute a simplified version of [P1 ∨ (a1 ≡ a2)]. *)
  Global Instance option_some_is_included a1 a2 P1 P2 :
    IsIncludedOrEq M a1 a2 P1 P2 →
    IsIncluded M (Some a1) (Some a2) P2 | 100.
  Proof.
    rewrite /IsIncluded option_validI => [[HP1 HP2]].
    iIntros "#Ha2". rewrite option_includedI.
    iApply bi.wand_iff_trans; last by iApply HP2.
    rewrite HP1. iSplit; iIntros "[Ha|$]"; iLeft; by iApply "Ha2".
  Qed.

  (** TODO: there used to be an explicit [IsIncluded M None ma True] instance here *)
  Global Instance option_some_none_excl_included_merge a :
    IsIncluded M (Some a) None False.
  Proof. rewrite /IsIncluded. rewrite option_includedI. eauto. Qed.
End optional.


(** Instances for [csumR]. It takes some effort to account for (almost) all
   combinations of constructors. We skip combinations with [CsumBot],
   since the user should have extracted a [False] from that combination. *)
From iris.algebra Require Import csum.

Section csum.
  Context {A B : cmra} {M : ucmra}.
  Implicit Types P : uPred M.
  Implicit Types a : A.
  Implicit Types b : B.

  (** [IsValidGives] instances. *)
  Global Instance csum_inl_valid_gives a1 a2 P :
    IsValidGives M a1 a2 P → 
    IsValidGives M (Cinl (B := B) a1) (Cinl a2) P.
  Proof. rewrite /IsValidGives -Cinl_op csum_validI // Ha. Qed.

  Global Instance csum_inr_valid_gives a1 a2 P :
    IsValidGives M a1 a2 P → 
    IsValidGives M (Cinr (A := B) a1) (Cinr a2) P.
  Proof. rewrite /IsValidGives -Cinr_op csum_validI // Ha. Qed.

  Global Instance csum_inl_inr_valid_gives a b :
    IsValidGives M (Cinl a) (Cinr b) False.
  Proof. rewrite /IsValidGives csum_validI. eauto. Qed.

  Global Instance csum_inr_inl_valid_gives a b :
    IsValidGives M (Cinr a) (Cinl b) False.
  Proof. rewrite /IsValidGives csum_validI. eauto. Qed.


  (** [IsValidOp] instances. *)
  Global Instance sum_inl_valid_op a a1 a2 :
    IsValidOp M a1 a2 a → 
    IsValidOp M (Cinl (B := B) a1) (Cinl a2) (Cinl a).
  Proof. by rewrite /IsValidOp -Cinl_op csum_validI csum_equivI => ->. Qed.

  Global Instance sum_inr_valid_op a a1 a2 :
    IsValidOp M a1 a2 a → 
    IsValidOp M (Cinr (A := B) a1) (Cinr a2) (Cinr a).
  Proof. by rewrite /IsValidOp -Cinr_op csum_validI csum_equivI => ->. Qed.

  Global Instance sum_inl_inr_valid_op a b :
    IsValidOp M (Cinl a) (Cinr b) CsumBot.
  Proof. rewrite /IsValidOp. eauto. Qed.

  Global Instance sum_inr_inl_valid_op a b :
    IsValidOp M (Cinr a) (Cinl b) CsumBot.
  Proof. rewrite /IsValidOp. eauto. Qed.


  (** [IsIncluded] instances.
     For these, it would be very helpful to make use of the fact that Cinl and
     Cinr are isomorphic. For now, we just repeat the proofs. *)
  Global Instance sum_inl_is_included a1 a2 P :
    IsIncluded M a1 a2 P →
    IsIncluded M (Cinl (B := B) a1) (Cinl (B := B) a2) P | 100.
  Proof.
    rewrite /IsIncluded => HaP.
    by rewrite csum_includedI csum_validI.
  Qed.

  Global Instance sum_inr_is_included b1 b2 P :
    IsIncluded M b1 b2 P →
    IsIncluded M (Cinr (A := A) b1) (Cinr (A := A) b2) P | 100.
  Proof.
    rewrite /IsIncluded => HaP.
    by rewrite csum_includedI csum_validI.
  Qed.

  Global Instance sum_inl_inr_is_included a b :
    IsIncluded M (Cinl a) (Cinr b) False | 100.
  Proof. rewrite /IsIncluded csum_includedI. eauto. Qed.

  Global Instance sum_inr_inl_is_included a b :
    IsIncluded M (Cinr b) (Cinl a) False | 100.
  Proof. rewrite /IsIncluded csum_includedI. eauto. Qed.

  (** [IsIncludedOrEq] instances.*)
  Global Instance sum_inl_is_included_or_eq a1 a2 P1 P2 :
    IsIncludedOrEq M a1 a2 P1 P2 →
    IsIncludedOrEq M (Cinl (B := B) a1) (Cinl (B := B) a2) P1 P2 | 105.
  Proof.
    case => HP_lt HP_le; split; first apply _.
    rewrite csum_validI HP_le.
    iApply bi.wand_iff_trans.
    iSplit; iIntros "[$|H]"; iRight; rewrite csum_equivI //.
  Qed.

  Global Instance sum_inr_is_included_or_eq b1 b2 P1 P2 :
    IsIncludedOrEq M b1 b2 P1 P2 →
    IsIncludedOrEq M (Cinr (A := A) b1) (Cinr (A := A) b2) P1 P2 | 105.
  Proof.
    case => HP_lt HP_le; split; first apply _.
    rewrite csum_validI HP_le.
    iApply bi.wand_iff_trans.
    iSplit; iIntros "[$|H]"; iRight; rewrite csum_equivI //.
  Qed.

  (** We also give instances for the invalid [Cinl _ ⋅ Cinr _] combinations,
    since the [Cinl _ ≡ Cinr _] simplification provided by the fallback
    instance [is_included_or_eq_last_resort] is not immediately helpful. *)
  Global Instance sum_inl_inr_is_included_or_eq a b :
    IsIncludedOrEq M (Cinl a) (Cinr b) False False.
  Proof.
    split; first apply _.
    rewrite csum_equivI right_id. eauto.
  Qed.

  Global Instance sum_inr_inl_is_included_or_eq a b :
    IsIncludedOrEq M (Cinr b) (Cinl a) False False.
  Proof.
    split; first apply _.
    rewrite csum_equivI right_id. eauto.
  Qed.

  (** We need to provide recursive [HasRightId] instances, so that the
     [is_included_or_eq_from_right_id] can kick in. *)
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


(** Instances for [prodR]. *)
Section prod.
  Context {X Y : cmra} {M : ucmra}.
  Implicit Types x : X.
  Implicit Types y : Y.
  Implicit Types P : uPred M.

  Global Instance prod_valid_gives x1 x2 y1 y2 P1 P2 P :
    IsValidGives M x1 x2 P1 → 
    IsValidGives M y1 y2 P2 → 
    MakeAnd P1 P2 P →
    IsValidGives M (x1, y1) (x2, y2) P.
  Proof.
    rewrite /IsValidGives /MakeAnd prod_validI /= => -> -> <-.
    by rewrite bi.intuitionistically_and.
  Qed.

  Global Instance prod_valid_op x x1 x2 y y1 y2:
    IsValidOp M x1 x2 x → 
    IsValidOp M y1 y2 y → 
    IsValidOp M (x1, y1) (x2, y2) (x, y).
  Proof. by rewrite /IsValidOp prod_validI prod_equivI /= => -> ->. Qed.

  Global Instance prod_is_included x1 x2 y1 y2 P1 P2 P :
    IsIncluded M x1 x2 P1 →
    IsIncluded M y1 y2 P2 →
    MakeAnd P1 P2 P →
    IsIncluded M (x1, y1) (x2, y2) P.
  Proof.
    rewrite /IsIncluded /MakeAnd => HP1 HP2 <-.
    rewrite bi.intuitionistically_and prod_validI /=.
    rewrite prod_includedI.
    iIntros "[#Hx✓ #Hy✓]"; iSplit => /=.
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

  (** This is the most tricky instance of the bunch.
    The goal of this instance is to obtain good assertions for, e.g.
    [Some (q, p) ≼ Some (q', p')] in the cmra [optionUR (prodR fracR positiveR]
    This simplifies to [(q < q' ∧ p < p') ∨ (q = q' ∧ p = p')]. Crucially,
    it does _not_ simplify to [q ≤ q' ∧ p ≤ p']: the (in)equalities must coincide!

    Note that this does not have [q ≤ q'] and [p ≤ p'] directly, which might be
    what the user is after! To fix this, we additionally include that fact.
    We also check whether the elements of the pair [HasRightId], to further
    simplify the resulting disjunction.
  *)
  Global Instance prod_is_included_or_eq x1 x2 y1 y2 P1_lt P1_le P2_lt P2_le 
      P_lt P_le P_le' P_lt_case P_lt_case' P_case :
    IsIncludedOrEq M x1 x2 P1_lt P1_le → 
    IsIncludedOrEq M y1 y2 P2_lt P2_le →
    MakeAnd P1_le P2_le P_le' →
    MakeAnd P1_lt P2_lt P_lt →
    TCIf (HasRightId x2) (TCEq P_lt_case' True%I) (TCEq P_lt_case' P1_lt) →
    TCIf (HasRightId y2) (TCEq P_lt_case P_lt_case') (MakeAnd P_lt_case' P2_lt P_lt_case) →
    MakeOr P_lt_case (x1 ≡ x2 ∧ y1 ≡ y2)%I P_case → 
    (** MakeOr will simplify True ∨ P ⊣⊢ True and False ∨ P ⊣⊢ P *)
    MakeAnd P_le' P_case P_le →
    IsIncludedOrEq M (x1, y1) (x2, y2) P_lt P_le.
  Proof.
    rewrite /MakeAnd /MakeOr /HasRightId => HP1 HP2 HP1P2 HP1P2' HTC1 HTC2 HPcase HPle.
    split.
    { apply: prod_is_included.
      * apply HP1.
      * apply HP2.
      * done. }
    rewrite prod_validI /= -HPle -HPcase -HP1P2 -HP1P2' prod_equivI /=.
    clear HPle HPcase HP1P2 HP1P2'.
    iIntros "[#H✓x #H✓y]".
    iAssert (✓ y2 ∗ ✓ x2)%I as "[H✓y2 H✓x2]"; first by eauto.
    case: HP1 => + HP1. rewrite {1}HP1.
    case: HP2 => + HP2. rewrite {1}HP2.
    rewrite /IsIncluded => HP1' HP2'.
    iSplit.
    - iIntros "[#[Hc1 Hc2]|#[Hc1 Hc2]] !>"; iSplit; [iSplit | | iSplit | eauto].
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

(** Extra instance because TC resolution gets confused for [ucmra]'s...
   TODO: Test if this is still necessary *)
Global Instance prod_included_merge_ucmra {X Y : ucmra} (x1 x2 : X) (y1 y2 : Y) {M} P1 P2 P :
  IsIncluded M x1 x2 P1 →
  IsIncluded M y1 y2 P2 →
  MakeAnd P1 P2 P →
  IsIncluded M (x1, y1) (x2, y2) P.
Proof. simple eapply prod_is_included. Qed.

Global Instance prod_valid_gives_ucmra M {X Y : ucmra} (x1 x2 : X) (y1 y2 : Y) P1 P2 P :
  IsValidGives M x1 x2 P1 → 
  IsValidGives M y1 y2 P2 → 
  MakeAnd P1 P2 P →
  IsValidGives M (x1, y1) (x2, y2) P.
Proof.
  rewrite /IsValidGives /MakeAnd prod_validI /= => -> -> <-.
  by rewrite bi.intuitionistically_and.
Qed.



(** Instances for [exclR]. *)
From iris.algebra Require Import excl.

Section excl.
  Context {O : ofe} {M : ucmra}.
  Implicit Types o : O.
  Implicit Types e : excl O.

  Global Instance excl_valid_gives e1 e2 :
    IsValidGives M e1 e2 False.
  Proof. rewrite /IsValidGives excl_validI. eauto. Qed.

  Global Instance excl_valid_op e1 e2 :
    IsValidOp M e1 e2 ExclBot.
  Proof. rewrite /IsValidOp excl_validI. eauto. Qed.

  Global Instance excl_is_included e1 e2 :
    IsIncluded M e1 e2 False.
  Proof.
    rewrite /IsIncluded. rewrite excl_validI excl_includedI. 
    destruct e2; eauto.
  Qed.

  (** This instance does not follow from the [IdFree] instance, since that one
     only applies if [o1 = o2] syntactically. Here, we receive that equality *)
  Global Instance excl_is_included_or_eq o1 o2 :
    IsIncludedOrEq M (Excl o1) (Excl o2) False (o1 ≡ o2).
  Proof.
    split; first apply _.
    iIntros "_"; iSplit.
    - iIntros "[[]|#H] !>". rewrite excl_equivI //.
    - iIntros "#H". iRewrite "H". eauto.
  Qed.
End excl.


(** Instances for [exclR]. *)
From iris.algebra Require Import agree.

Section agree.
  Context {O : ofe} {M : ucmra}.
  Implicit Types o : O.

  Global Instance agree_valid_gives o1 o2 :
    IsValidGives M (to_agree o1) (to_agree o2) (o1 ≡ o2).
  Proof. rewrite /IsValidGives agree_validI agree_equivI. eauto. Qed.

  Global Instance agree_valid_op o1 o2 :
    IsValidOp M (to_agree o1) (to_agree o2) (to_agree o1).
  Proof.
    rewrite /IsValidOp agree_validI agree_equivI.
    iIntros "H".
    iRewrite "H".
    by rewrite agree_idemp.
  Qed.

  (** If two [a : agree O] compose to a [to_agree o], they are internally equal
     and also equal to [to_agree o]. This turns out to be a useful lemma. *)
  Lemma agree_op_equiv_to_agreeI (a1 a2 : agree O) o : 
    a1 ⋅ a2 ≡ to_agree o ⊢@{uPredI M} a1 ≡ a2 ∧ a2 ≡ to_agree o.
  Proof.
    iIntros "#Heq".
    iAssert (a1 ≡ a2)%I as "#H".
    - iApply agree_validI.
      by iRewrite "Heq".
    - iFrame "H". iRewrite -"Heq". iRewrite "H". rewrite agree_idemp //.
  Qed.

  (** We provide a higher cost [IsIncluded] instance for abstract [a : agree O]. *)
  Global Instance agree_is_included_abstract o1 (a : agree O) :
    IsIncluded M (to_agree o1) a (a ≡ to_agree o1) | 20.
  Proof.
    rewrite /IsIncluded. rewrite to_agree_uninjI. iIntros "[%o Ho]". 
    iRewrite -"Ho". rewrite agree_includedI. iSplit. 
    - rewrite internal_eq_sym agree_op_equiv_to_agreeI.
      rewrite internal_eq_sym. iIntros "[H _]". by iRewrite "H".
    - iIntros "#H". iRewrite "H". by rewrite agree_idemp.
  Qed.

  (** .. and a lower cost instance for concrete objects beneath a [to_agree]. *)
  Global Instance agree_is_included o1 o2 :
    IsIncluded M (to_agree o1) (to_agree o2) (o1 ≡ o2) | 10.
  Proof.
    eapply is_included_weaken, _. rewrite agree_equivI.
    iIntros "_"; iSplit; iIntros "#H"; by iRewrite "H".
  Qed.

  (** We don't provide an [IsIncludedOrEq] instance, since agree [HasRightId] *)
  Global Instance agree_has_right_id (a : agree O) : HasRightId a.
  Proof. exists a. by rewrite agree_idemp. Qed.
End agree.


(** Instances for [gmapR]. This is a [ucmra], so [IsIncludedOrEq] is omitted. *)
From iris.algebra Require Import gmap.

Section gmap.
  Context `{Countable K} {A : cmra} {M : ucmra}.
  Implicit Types m : gmap K A.
  Implicit Types k : K.
  Implicit Types a : A.

  (** TODO: move these to algebra/gmap? *)
  Global Instance gmap_is_op m m1 m2 :
    IsOp (merge op m1 m2) m1 m2 | 20.
  Proof. rewrite /IsOp //. Qed.
  Global Instance gmap_is_op_unit_l m :
    IsOp m m ∅ | 10.
  Proof. rewrite /IsOp right_id //. Qed.
  Global Instance gmap_is_op_unit_r m :
    IsOp m ∅ m | 10.
  Proof. rewrite /IsOp left_id //. Qed.

  Global Instance gmap_valid_gives m1 m2 :
    IsValidGives M m1 m2 True | 10.
  Proof. eauto. Qed.

  Global Instance gmap_valid_op m1 m2 m :
    IsOp m m1 m2 → IsValidOp M m1 m2 m | 10.
  Proof. apply from_isop. Qed.

  (** Two [IsIncluded] instance: the general one, and one for the singleton map. *)
  Global Instance gmap_is_included m1 m2 : 
    IsIncluded M m1 m2 (∃ m, ∀ i, m2 !! i ≡ m1 !! i ⋅ m !! i) | 100.
  Proof. 
    rewrite /IsIncluded. iIntros "_"; iSplit.
    - iIntros "[%m #Hm] !>". iExists (m).
      iIntros (i). rewrite gmap_equivI -lookup_op. iApply "Hm".
    - iIntros "[%m #Hm]". iExists (m). rewrite gmap_equivI.
      iIntros (i). rewrite lookup_op. iApply "Hm".
  Qed.

  Global Instance gmap_included_merge_singleton m k a : 
    IsIncluded M {[ k := a ]} m (∃ a', m !! k ≡ Some a' ∧ Some a ≼ Some a' )%I | 50.
     (* if m !! k would reduce, we could do better *)
  Proof.
    eapply is_included_weaken, _.
    iIntros "#H✓"; iSplit.
    - iIntros "[%m' #Hm] !>".
      iSpecialize ("Hm" $! k). rewrite lookup_singleton //.
      rewrite Some_op_opM.
      iExists (a ⋅? _). iFrame "Hm".
      iExists (m' !! k). rewrite Some_op_opM //.
    - iIntros "#[%a' [Hk [%ma Hma]]] !>".
      rewrite Some_op_opM (option_equivI (Some a')).
      destruct ma as [a''| ] => /=.
      * iExists (<[k := a'']> m). iIntros (i).
        destruct (decide (k = i)) as [-> | Hneq].
        + rewrite lookup_singleton lookup_insert.
          iRewrite "Hk". by iApply option_equivI.
        + rewrite lookup_singleton_ne // left_id lookup_insert_ne //.
      * iExists (delete k m). iIntros (i).
        destruct (decide (k = i)) as [-> | Hneq].
        + rewrite lookup_singleton lookup_delete // right_id. by iRewrite -"Hma".
        + rewrite lookup_singleton_ne // left_id lookup_delete_ne //.
  Qed.
End gmap.


(** Instances for [viewR]. We do not provide [IsIncluded] instances, since
   that would be involved and only used for ghost state of the form [● (●V a)],
   which we believe to be rare. *)
From iris.algebra Require Import view.

Section view.
  Context {A : ofe} {B M : ucmra} {rel : view_rel A B}.
  Implicit Types a : A.
  Implicit Types b : B.
  Implicit Types P : uPred M.
  Implicit Types v : viewR rel.

  (** We embed the view relation in the logic, so we can state and work with it
     without dropping down to the model *)
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

  (** TODO: Move below lemmas to some better place? *)
  Lemma view_validI v :
    ✓ v ⊣⊢@{uPredI M} match view_auth_proj v with
          | Some (dq, a) =>
            ∃ a', a ≡ to_agree a' ∧ v ≡ ●V{dq} a' ⋅ ◯V (view_frag_proj v) ∧ 
                  rel_holds_for a' (view_frag_proj v) ∧ ✓ dq
          | None => v ≡ ◯V (view_frag_proj v) ∧ 
                  ∃ a, rel_holds_for a (view_frag_proj v)
          end.
  Proof.
    destruct v as [[[dq a]|] b] => /=.
    - uPred.unseal.
      split=> n y Hy.
      split.
      * case => Hdq [a' [Ha1 Ha2]].
        repeat (rewrite /uPred_holds /=).
        exists a'.
        split; first done.
        split; last done.
        rewrite Ha1 /op /cmra_op /= /view_op_instance /= right_id left_id //.
      * repeat (rewrite /uPred_holds /=).
        rewrite /upred.uPred_cmra_valid_def /validN /cmra_validN /=
           /view_validN_instance /=. naive_solver.
    - uPred.unseal. split => n y Hy //=.
      repeat (rewrite /uPred_holds /=). naive_solver.
  Qed.

  Lemma view_equivI v1 v2 :
    v1 ≡ v2 ⊣⊢@{uPredI M} view_auth_proj v1 ≡ view_auth_proj v2 ∧ 
                          view_frag_proj v1 ≡ view_frag_proj v2.
  Proof. by uPred.unseal. Qed.

  Lemma view_auth_dfrac_op_validI dq1 dq2 a1 a2 : 
    ✓ (view_auth (rel := rel) dq1 a1 ⋅ ●V{dq2} a2) ⊣⊢@{uPredI M} 
      ✓ (dq1 ⋅ dq2) ∧ (a1 ≡ a2) ∧ rel_holds_for a2 ε.
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
      iDestruct 1 as (a) "Ha". 
      rewrite agree_op_equiv_to_agreeI !agree_equivI /= right_id.
      iDestruct "Ha" as "([$ #Heq] & _ & H & $)".
      iRewrite "Heq". eauto.
  Qed.

  Global Instance view_frag_valid_gives b b1 b2 :
    IsOp b b1 b2 →
    IsValidGives M (view_frag (rel := rel) b1) (◯V b2) (∃ a, rel_holds_for a b)%I.
  Proof.
    rewrite /IsOp /IsValidGives => Hb.
    rewrite view_validI /= -view_frag_op.
    iDestruct 1 as "[_ [%a #Ha]]". rewrite -Hb. eauto.
  Qed.

  Global Instance view_frag_valid_op b b1 b2 :
    IsOp b b1 b2 →
    IsValidOp M (◯V b1) (◯V b2) (view_frag (rel := rel) b).
  Proof. rewrite /IsOp /IsValidOp -view_frag_op /= => <-. eauto. Qed.

  Global Instance view_auth_valid_gives a1 a2 dq1 dq2 Pq :
    IsValidGives M dq1 dq2 Pq →
    IsValidGives M (view_auth (rel := rel) dq1 a1) (●V{dq2} a2) 
                    (Pq ∧ a1 ≡ a2 ∧ rel_holds_for a2 ε)%I.
  Proof.
    rewrite /IsValidGives view_auth_dfrac_op_validI => ->.
    iIntros "(#$ & #$ & #$)".
  Qed.

  Global Instance view_auth_dfrac_own_valid_op a1 a2 dq dq1 dq2 :
    IsValidOp M dq1 dq2 dq →
    IsValidOp M (view_auth (rel := rel) dq1 a1) (●V{dq2} a2) (●V{dq} a1).
  Proof.
    rewrite /IsValidOp view_auth_dfrac_op_validI => ->.
    iIntros "(-> & Heq & _)".
    iRewrite "Heq".
    rewrite -view_auth_dfrac_op //.
  Qed.

  Global Instance view_auth_frag_valid_gives dq a b :
    IsValidGives M (view_auth (rel := rel) dq a) (◯V b) (rel_holds_for a b).
  Proof.
    rewrite /IsValidGives.
    rewrite view_validI /=.
    iIntros "[%a' [#Ha [_ [#Hc _]]]]".
    rewrite agree_equivI left_id.
    by iRewrite "Ha". 
  Qed.

  Global Instance view_frag_auth_valid_gives dq a b :
    IsValidGives M (◯V b) (view_auth (rel := rel) dq a) (rel_holds_for a b).
  Proof. apply is_valid_gives_comm, _. Qed.
End view.

Global Arguments rel_holds_for {A B M} rel _ _.


(** Instances for [authR]. Like for [viewR], we do not provide instances for
   [IsIncluded]. *)
From iris.algebra Require Import auth.

Section auth.
  Context {A M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  Lemma auth_rel_holds a1 a2 : 
    rel_holds_for auth_view_rel a1 a2 ⊣⊢@{uPredI M} a2 ≼ a1 ∧ ✓ a1.
  Proof. rewrite internal_included_def. by uPred.unseal. Qed.

  Lemma auth_auth_dfrac_op_validI dq1 dq2 a1 a2 : 
    ✓ (●{dq1} a1 ⋅ ●{dq2} a2) ⊣⊢@{uPredI M} ✓ (dq1 ⋅ dq2) ∧ ✓ a2 ∧ (a1 ≡ a2).
  Proof.
    rewrite view_auth_dfrac_op_validI auth_rel_holds.
    eapply (anti_symm _); eauto with iFrame.
    - iIntros "($ & $ & _ & $)".
    - iIntros "($ & $ & $)". iExists a2. by rewrite left_id.
  Qed.


  (** [IsValidGives] instances. *)
  Global Instance auth_frag_valid_gives a1 a2 P :
    IsValidGives M a1 a2 P →
    IsValidGives M (◯ a1) (◯ a2) P.
  Proof. by rewrite /IsValidGives -auth_frag_op auth_frag_validI. Qed.

  Global Instance auth_auth_valid_gives a1 a2 dq1 dq2 Pq :
    IsValidGives M dq1 dq2 Pq →
    IsValidGives M (●{dq1} a1) (●{dq2} a2) (Pq ∧ a1 ≡ a2).
  Proof.
    move => Hq. rewrite /auth_auth.
    eapply is_valid_gives_weaken, _.
    iIntros "[_ #($ & $ & _)]".
  Qed.

  Global Instance auth_auth_frag_valid_gives dq a1 a2 P :
    IsIncluded M a2 a1 P →
    IsValidGives _ (●{dq} a1) (◯ a2) P.
  Proof.
    rewrite /IsIncluded => HP. rewrite /auth_auth /auth_frag.
    eapply is_valid_gives_weaken, _. rewrite auth_rel_holds.
    rewrite view_validI /= HP. iIntros "[_ [#H1 #H2]]".
    iApply bi.intuitionistically_elim. by iApply "H2".
  Qed.

  Global Instance auth_frag_auth_valid_gives dq a1 a2 P :
    IsIncluded M a2 a1 P →
    IsValidGives _ (◯ a2) (●{dq} a1) P.
  Proof. intros; eapply is_valid_gives_comm, _. Qed.


  (** [IsValidOp] instances. *)
  Global Instance auth_frag_valid_op a a1 a2 :
    IsValidOp M a1 a2 a →
    IsValidOp M (◯ a1) (◯ a2) (◯ a).
  Proof.
    rewrite /IsValidOp -auth_frag_op auth_frag_validI => ->.
    iIntros "H". by iRewrite "H".
  Qed.

  Global Instance auth_auth_dfrac_own_valid_op a1 a2 dq dq1 dq2 :
    IsValidOp M dq1 dq2 dq →
    IsValidOp M (●{dq1} a1) (●{dq2} a2) (●{dq} a1).
  Proof. move => Hq. rewrite /auth_auth. apply _. Qed.
End auth.


(** Instances for [frac_authR], obtained by unfolding to [authR]. *)
From iris.algebra.lib Require Import frac_auth.

Section frac_auth.
  Context {A : cmra} {M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  (* overcomes the typeclasses opaque instance on frac_auth_frag *)
  Global Instance frac_auth_frag_valid_gives a1 a2 (q1 q2 : Qp) P1 P2 :
    IsValidGives M q1 q2 P1 →
    IsValidGives M a1 a2 P2 →
    IsValidGives M (◯F{q1} a1) (◯F{q2} a2) (P1 ∧ P2).
  Proof. intros. rewrite /frac_auth_frag. apply _. Qed.

  Global Instance frac_auth_auth_frag_valid_gives q a1 a2 P :
    IsIncluded M (Some (q, a2)) (Some (1%Qp, a1)) P →
    IsValidGives _ (●F a1) (◯F{q} a2) P.
  Proof. rewrite /frac_auth_frag /frac_auth_auth. apply _. Qed.

  Global Instance frac_auth_frag_auth_valid_gives q a1 a2 P :
    IsIncluded M (Some (q, a2)) (Some (1%Qp, a1)) P →
    IsValidGives _ (◯F{q} a2) (●F a1) P.
  Proof. intros; eapply is_valid_gives_comm, _. Qed.

  Global Instance frac_auth_auth_valid_gives a1 a2 :
    IsValidGives M (●F a1) (●F a2) False.
  Proof.
    rewrite /frac_auth_auth.
    eapply is_valid_gives_weaken, _.
    iIntros "[_ [%H _]]".
    contradict H. eauto.
  Qed.

  Global Instance frac_auth_frag_valid_op a a1 a2 (q q1 q2 : Qp) :
    IsValidOp M q1 q2 q →
    IsValidOp M a1 a2 a →
    IsValidOp M (◯F{q1} a1) (◯F{q2} a2) (◯F{q} a).
  Proof. move => Hq Ha. rewrite /frac_auth_frag. apply _. Qed.
End frac_auth.


(** Instances for [excl_authR], again obtained by unfolding to [authR]. *)
From iris.algebra.lib Require Import excl_auth.

Section excl_auth.
  Context {A : ofe} {M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  Global Instance excl_auth_frag_valid_gives a1 a2 P :
    IsValidGives M (Excl' a1) (Excl' a2) P →
    IsValidGives M (◯E a1) (◯E a2) P.
  Proof. rewrite /excl_auth_frag. apply _. Qed.

  Global Instance excl_auth_auth_frag_valid_gives a1 a2 P :
    IsIncluded M (Excl' a2) (Excl' a1) P →
    IsValidGives M (●E a1) (◯E a2) P.
  Proof. rewrite /excl_auth_auth /excl_auth_frag. apply _. Qed.

  Global Instance excl_auth_frag_is_valid_gives_swap a1 a2 P :
    IsIncluded M (Excl' a2) (Excl' a1) P →
    IsValidGives M (◯E a2) (●E a1) P.
  Proof. intros; eapply is_valid_gives_comm, _. Qed.

  Global Instance excl_auth_auth_valid_gives a1 a2 :
    IsValidGives M (●E a1) (●E a2) False.
  Proof.
    rewrite /excl_auth_auth.
    eapply is_valid_gives_weaken, _.
    iIntros "[_ [%H _]]". contradict H. eauto.
  Qed.

  Global Instance excl_auth_frag_valid_op ea a1 a2 :
    IsValidOp M (Excl' a1) (Excl' a2) (Some ea) →
    IsValidOp M (◯E a1) (◯E a2) (◯ (Some ea)) .
  Proof. rewrite /excl_auth_frag. apply _. Qed.
End excl_auth.


(** Instances for [dfrac_agreeR], again obtained by unfolding the definition. *)
From iris.algebra.lib Require Import dfrac_agree.

Section dfrac_agree.
  Context {A : ofe} {M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  Global Instance dfrac_agree_valid_gives q1 a1 q2 a2 P :
    IsValidGives M (q1, to_agree a1) (q2, to_agree a2) P →
    IsValidGives M (to_dfrac_agree q1 a1) (to_dfrac_agree q2 a2) P.
  Proof. by rewrite /to_dfrac_agree. Qed.

  Global Instance dfrac_agree_valid_op q a q1 a1 q2 a2 :
    IsValidOp M (q1, to_agree a1) (q2, to_agree a2) (q, to_agree a) →
    IsValidOp M (to_dfrac_agree q1 a1) (to_dfrac_agree q2 a2) (to_dfrac_agree q a).
  Proof. by rewrite /to_dfrac_agree. Qed.

  Global Instance dfrac_agree_is_included q1 a1 q2 a2 P :
    IsIncluded M (q1, to_agree a1) (q2, to_agree a2) P →
    IsIncluded M (to_dfrac_agree q1 a1) (to_dfrac_agree q2 a2) P.
  Proof. by rewrite /to_dfrac_agree. Qed.

  Global Instance dfrac_agree_is_included_or_eq q1 a1 q2 a2 P1 P2 :
    IsIncludedOrEq M (q1, to_agree a1) (q2, to_agree a2) P1 P2 →
    IsIncludedOrEq M (to_dfrac_agree q1 a1) (to_dfrac_agree q2 a2) P1 P2.
  Proof. by rewrite /to_dfrac_agree. Qed.
End dfrac_agree.


(** Instances for [gmap_viewR]. This is a [ucmra], so [IsIncludedOrEq] is omitted. *)
From iris.algebra.lib Require Import gmap_view.

Section gmap_view.
  Context {K : Type} `{Countable K} {V : ofe} {M : ucmra}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dq : dfrac) (v : V).
  Implicit Types P : uPred M.

  Lemma gmap_view_rel_holds (m : gmap K V) (f : gmap K (dfrac * agree V)) : 
    rel_holds_for (gmap_view.gmap_view_rel K V) m f ⊣⊢@{uPredI M} 
      ∀ (i : K) dq a, 
        ⌜f !! i = Some (dq, a)⌝ → 
        ∃ a', a ≡ to_agree a' ∧ ✓ dq ∧ ⌜m !! i = Some a'⌝.
  Proof. 
    split => n x Hx. uPred.unseal.
    repeat (rewrite /uPred_holds /=).
    rewrite /gmap_view.gmap_view_rel_raw /=. split.
    - move => /map_Forall_lookup Hm k dq a n' x' Hx' Hn Hx'' /Hm /= 
           => [[v [Hv1 [Hv2 Hv3]]]].
      exists v. rewrite Hv3. split; eauto using dist_le'.
    - move => H0. apply map_Forall_lookup => k [dq a] /= /H0 {H0} H0'.
      destruct (H0' n x) as [v Hv]; eauto.
  Qed.

  Lemma gmap_view_rel_holds_singleton k dv m :
    rel_holds_for (gmap_view.gmap_view_rel K V) m {[ k := dv ]} ⊣⊢@{uPredI M} 
      ∃ a', dv.2 ≡ to_agree a' ∧ ✓ dv.1 ∧ ⌜m !! k = Some a'⌝.
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


  (** [IsValidGives] instances. *)
  Global Instance gmap_view_frag_valid_gives k dq1 dq2 v1 v2 P :
    IsValidGives M dq1 dq2 P →
    IsValidGives M (gmap_view_frag k dq1 v1) (gmap_view_frag k dq2 v2) 
                  (P ∧ v1 ≡ v2).
  Proof.
    rewrite /IsValidGives view_validI /= => HP.
    iDestruct 1 as "[_ [%m Hm]]".
    rewrite singleton_op -pair_op gmap_view_rel_holds_singleton /=.
    iDestruct "Hm" as "[%v3 (#Hv3 & Hv3' & _)]".
    rewrite agree_op_equiv_to_agreeI HP bi.and_elim_l 
      agree_equivI bi.intuitionistically_and.
    eauto.
  Qed.

  Global Instance gmap_view_auth_valid_gives dq1 dq2 P m1 m2 :
    IsValidGives M dq1 dq2 P →
    IsValidGives M (gmap_view_auth dq1 m1) (gmap_view_auth dq2 m2) (P ∧ m1 ≡ m2).
  Proof.
    intros. rewrite /gmap_view_auth.
    eapply is_valid_gives_weaken, _.
    iIntros "(_ & #$ & #$ & _ )".
  Qed.

  Global Instance gmap_view_auth_frag_valid_gives dq1 m k dq2 v :
    IsValidGives M (gmap_view_auth dq1 m) (gmap_view_frag k dq2 v) 
                   (m !! k ≡ Some v).
  Proof.
    rewrite /IsValidGives view_validI /=.
    iDestruct 1 as (m') "(Hm' & _ & Hr & _)".
    iRevert "Hr". rewrite agree_equivI. iRewrite -"Hm'". clear m'.
    rewrite left_id gmap_view_rel_holds_singleton.
    iDestruct 1 as (v') "(Hv1 & Hv2 & ->)". simpl.
    rewrite agree_equivI. by iRewrite "Hv1".
  Qed.

  Global Instance gmap_view_frag_auth_valid_gives dq1 m k dq2 v :
    IsValidGives M (gmap_view_frag k dq2 v) (gmap_view_auth dq1 m) 
                   (m !! k ≡ Some v).
  Proof. apply is_valid_gives_comm, _. Qed.


  (** [IsValidOp] instances. *)
  Global Instance gmap_view_frag_valid_op k dq dq1 dq2 v1 v2 :
    IsValidOp M dq1 dq2 dq →
    IsValidOp M (gmap_view_frag k dq1 v1) (gmap_view_frag k dq2 v2) 
                  (gmap_view_frag k dq v1).
  Proof.
    rewrite /IsValidOp => H0. rewrite view_validI /=.
    iDestruct 1 as "[_ [%m Hm]]".
    rewrite singleton_op -pair_op gmap_view_rel_holds_singleton /=.
    iDestruct "Hm" as "[%v3 (Hv3 & Hv3' & _)]".
    rewrite agree_op_equiv_to_agreeI H0 bi.and_elim_l agree_equivI.
    iRewrite "Hv3". iRewrite "Hv3'". rewrite -gmap_view_frag_op //.
  Qed.

  Global Instance gmap_view_auth_valid_op dq dq1 dq2 m1 m2 :
    IsValidOp M dq1 dq2 dq →
    IsValidOp M (gmap_view_auth dq1 m1) (gmap_view_auth dq2 m2) 
                (gmap_view_auth dq m1).
  Proof.
    intros. rewrite /gmap_view_auth.
    eapply is_valid_op_change, _. eauto.
  Qed.
End gmap_view.

