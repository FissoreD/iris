From iris.base_logic Require Export bi.
From iris.bi Require Export bi.
Set Default Proof Using "Type".
Import bi.

Module uPred.

(* New unseal tactic that also unfolds the BI layer *)
Ltac unseal := (* Coq unfold is used to circumvent bug #5699 in rewrite /foo *)
  unfold bi_emp; simpl; unfold sbi_emp; simpl;
  unfold uPred_emp, bupd, bi_bupd_bupd, bi_pure,
  bi_and, bi_or, bi_impl, bi_forall, bi_exist,
  bi_sep, bi_wand, bi_persistently, sbi_internal_eq, sbi_later; simpl;
  unfold sbi_emp, sbi_pure, sbi_and, sbi_or, sbi_impl, sbi_forall, sbi_exist,
  sbi_internal_eq, sbi_sep, sbi_wand, sbi_persistently; simpl;
  unfold plainly, bi_plainly_plainly; simpl;
  uPred_primitive.unseal.

Section derived.
Context {M : ucmraT}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P%I Q%I).
Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).

(** Propers *)
Global Instance uPred_valid_proper : Proper ((⊣⊢) ==> iff) (@uPred_valid M).
Proof. solve_proper. Qed.
Global Instance uPred_valid_mono : Proper ((⊢) ==> impl) (@uPred_valid M).
Proof. solve_proper. Qed.
Global Instance uPred_valid_flip_mono :
  Proper (flip (⊢) ==> flip impl) (@uPred_valid M).
Proof. solve_proper. Qed.

Global Existing Instance uPred_primitive.ownM_ne.
Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@uPred_ownM M) := ne_proper _.

Global Existing Instance uPred_primitive.cmra_valid_ne.
Global Instance cmra_valid_proper {A : cmraT} :
  Proper ((≡) ==> (⊣⊢)) (@uPred_cmra_valid M A) := ne_proper _.

(** Re-exporting primitive Own and valid lemmas *)
Lemma ownM_op (a1 a2 : M) :
  uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
Proof. exact: uPred_primitive.ownM_op. Qed.
Lemma persistently_ownM_core (a : M) : uPred_ownM a ⊢ <pers> uPred_ownM (core a).
Proof. exact: uPred_primitive.persistently_ownM_core. Qed.
Lemma ownM_unit P : P ⊢ (uPred_ownM ε).
Proof. exact: uPred_primitive.ownM_unit. Qed.
Lemma later_ownM a : ▷ uPred_ownM a ⊢ ∃ b, uPred_ownM b ∧ ▷ (a ≡ b).
Proof. exact: uPred_primitive.later_ownM. Qed.
Lemma bupd_ownM_updateP x (Φ : M → Prop) :
  x ~~>: Φ → uPred_ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ uPred_ownM y.
Proof. exact: uPred_primitive.bupd_ownM_updateP. Qed.

Lemma ownM_valid (a : M) : uPred_ownM a ⊢ ✓ a.
Proof. exact: uPred_primitive.ownM_valid. Qed.
Lemma cmra_valid_intro {A : cmraT} P (a : A) : ✓ a → P ⊢ (✓ a).
Proof. exact: uPred_primitive.cmra_valid_intro. Qed.
Lemma cmra_valid_elim {A : cmraT} (a : A) : ¬ ✓{0} a → ✓ a ⊢ False.
Proof. exact: uPred_primitive.cmra_valid_elim. Qed.
Lemma plainly_cmra_valid_1 {A : cmraT} (a : A) : ✓ a ⊢ ■ ✓ a.
Proof. exact: uPred_primitive.plainly_cmra_valid_1. Qed.
Lemma cmra_valid_weaken {A : cmraT} (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
Proof. exact: uPred_primitive.cmra_valid_weaken. Qed.
Lemma prod_validI {A B : cmraT} (x : A * B) : ✓ x ⊣⊢ ✓ x.1 ∧ ✓ x.2.
Proof. exact: uPred_primitive.prod_validI. Qed.
Lemma option_validI {A : cmraT} (mx : option A) :
  ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True : uPred M end.
Proof. exact: uPred_primitive.option_validI. Qed.
Lemma discrete_valid {A : cmraT} `{!CmraDiscrete A} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
Proof. exact: uPred_primitive.discrete_valid. Qed.
Lemma ofe_fun_validI `{B : A → ucmraT} (g : ofe_fun B) : ✓ g ⊣⊢ ∀ i, ✓ g i.
Proof. exact: uPred_primitive.ofe_fun_validI. Qed.

(** Own and valid derived *)
Lemma persistently_cmra_valid_1 {A : cmraT} (a : A) : ✓ a ⊢ <pers> (✓ a : uPred M).
Proof. by rewrite {1}plainly_cmra_valid_1 plainly_elim_persistently. Qed.
Lemma intuitionistically_ownM (a : M) : CoreId a → □ uPred_ownM a ⊣⊢ uPred_ownM a.
Proof.
  rewrite /bi_intuitionistically affine_affinely=>?; apply (anti_symm _);
    [by rewrite persistently_elim|].
  by rewrite {1}persistently_ownM_core core_id_core.
Qed.
Lemma ownM_invalid (a : M) : ¬ ✓{0} a → uPred_ownM a ⊢ False.
Proof. by intros; rewrite ownM_valid cmra_valid_elim. Qed.
Global Instance ownM_mono : Proper (flip (≼) ==> (⊢)) (@uPred_ownM M).
Proof. intros a b [b' ->]. by rewrite ownM_op sep_elim_l. Qed.
Lemma ownM_unit' : uPred_ownM ε ⊣⊢ True.
Proof. apply (anti_symm _); first by apply pure_intro. apply ownM_unit. Qed.
Lemma plainly_cmra_valid {A : cmraT} (a : A) : ■ ✓ a ⊣⊢ ✓ a.
Proof. apply (anti_symm _), plainly_cmra_valid_1. apply plainly_elim, _. Qed.
Lemma intuitionistically_cmra_valid {A : cmraT} (a : A) : □ ✓ a ⊣⊢ ✓ a.
Proof.
  rewrite /bi_intuitionistically affine_affinely. intros; apply (anti_symm _);
    first by rewrite persistently_elim.
  apply:persistently_cmra_valid_1.
Qed.
Lemma bupd_ownM_update x y : x ~~> y → uPred_ownM x ⊢ |==> uPred_ownM y.
Proof.
  intros; rewrite (bupd_ownM_updateP _ (y =)); last by apply cmra_update_updateP.
  by apply bupd_mono, exist_elim=> y'; apply pure_elim_l=> ->.
Qed.

(* Timeless instances *)
Global Instance valid_timeless {A : cmraT} `{CmraDiscrete A} (a : A) :
  Timeless (✓ a : uPred M)%I.
Proof. rewrite /Timeless !discrete_valid. apply (timeless _). Qed.
Global Instance ownM_timeless (a : M) : Discrete a → Timeless (uPred_ownM a).
Proof.
  intros ?. rewrite /Timeless later_ownM. apply exist_elim=> b.
  rewrite (timeless (a≡b)) (except_0_intro (uPred_ownM b)) -except_0_and.
  apply except_0_mono. rewrite internal_eq_sym.
  apply (internal_eq_rewrite' b a (uPred_ownM) _);
    auto using and_elim_l, and_elim_r.
Qed.

(* Plainness *)
Global Instance cmra_valid_plain {A : cmraT} (a : A) :
  Plain (✓ a : uPred M)%I.
Proof. rewrite /Persistent. apply plainly_cmra_valid_1. Qed.

(* Persistence *)
Global Instance cmra_valid_persistent {A : cmraT} (a : A) :
  Persistent (✓ a : uPred M)%I.
Proof. rewrite /Persistent. apply persistently_cmra_valid_1. Qed.
Global Instance ownM_persistent a : CoreId a → Persistent (@uPred_ownM M a).
Proof.
  intros. rewrite /Persistent -{2}(core_id_core a). apply persistently_ownM_core.
Qed.

(* For big ops *)
Global Instance uPred_ownM_sep_homomorphism :
  MonoidHomomorphism op uPred_sep (≡) (@uPred_ownM M).
Proof. split; [split; try apply _|]. apply ownM_op. apply ownM_unit'. Qed.
End derived.

(* Also add this to the global hint database, otherwise [eauto] won't work for
many lemmas that have [BiAffine] as a premise. *)
Hint Immediate uPred_affine.
End uPred.
