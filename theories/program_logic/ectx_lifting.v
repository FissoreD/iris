(** Some derived lemmas for ectx-based languages *)
From iris.program_logic Require Export ectx_language weakestpre lifting.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section wp.
Context {expr val ectx state} {Λ : EctxLanguage expr val ectx state}.
Context `{irisG (ectx_lang expr) Σ} {Hinh : Inhabited state}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.
Hint Resolve head_prim_reducible head_reducible_prim_step.

Lemma wp_ectx_bind {E Φ} K e :
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
Proof. apply: weakestpre.wp_bind. Qed.

Lemma wp_ectx_bind_inv {E Φ} K e :
  WP fill K e @ E {{ Φ }} ⊢ WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }}.
Proof. apply: weakestpre.wp_bind_inv. Qed.

Lemma wp_lift_head_step {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (wp_lift_step E)=>//. iIntros (σ1) "Hσ".
  iMod ("H" $! σ1 with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by eauto. iNext. iIntros (e2 σ2 efs) "%".
  iApply "H". by eauto.
Qed.

Lemma wp_lift_pure_head_step {E E' Φ} e1 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (|={E,E'}▷=> ∀ e2 efs σ, ⌜head_step e1 σ e2 σ efs⌝ →
    WP e2 @ E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof using Hinh.
  iIntros (??) "H". iApply wp_lift_pure_step; eauto.
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (????). iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗ [∗ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by eauto. iNext. iIntros (e2 σ2 efs) "%". iApply "H"; auto.
Qed.

Lemma wp_lift_atomic_head_step_no_fork {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 ∗ default False (to_val e2) Φ)
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 efs) "%".
  iMod ("H" $! v2 σ2 efs with "[# //]") as "(% & $ & $)"; subst; auto.
Qed.

Lemma wp_lift_pure_det_head_step {E E' Φ} e1 e2 efs :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
  (|={E,E'}▷=> WP e2 @ E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof using Hinh. eauto using wp_lift_pure_det_step. Qed.

Lemma wp_lift_pure_det_head_step_no_fork {E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  (|={E,E'}▷=> WP e2 @ E {{ Φ }}) ⊢ WP e1 @ E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step e1 e2 []) /= ?right_id; eauto.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork' {E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  ▷ WP e2 @ E {{ Φ }} ⊢ WP e1 @ E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ _ {{ _ }})%I]wp_lift_pure_det_head_step_no_fork //.
  rewrite -step_fupd_intro //.
Qed.
End wp.
