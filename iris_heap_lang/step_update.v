From iris.bi Require Import updates.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import primitive_laws.
From iris.prelude Require Import options.

Set Default Proof Using "Type".

Section with_Σ.
  Context `{!heapGS_gen hlc Σ}.

  (* TODO: Move/Rename these *)
  Lemma step_fupdN_frame_l' Eo Ei n (R Q : iProp Σ) :
    (▷^n R ∗ |={Eo}[Ei]▷=>^n Q) -∗ |={Eo}[Ei]▷=>^n (R ∗ Q).
  Proof.
    induction n as [|n IH]; simpl; [done|].
    iIntros "[HR HQ]".
    iApply IH. by iFrame.
  Qed.

  Lemma step_fupdN_empty_sep n (R Q : iProp Σ) :
    (|={∅}▷=>^n R) ∗ (|={∅}▷=>^n Q) -∗ |={∅}▷=>^n (R ∗ Q).
  Proof.
    induction n as [|n IH]; simpl; [done|].
    iIntros "[HR HQ]". iApply IH.
    iMod "HR". iMod "HQ". iIntros "!>!>". iMod "HR". iMod "HQ". by iFrame.
  Qed.

  Definition step_update E1 E2 P : iProp Σ :=
    ∀ n, primitive_laws.steps_auth n ={E1,E2}=∗
         (primitive_laws.steps_auth n ∗
          (|={∅}▷=>^(S n) (primitive_laws.steps_auth (S n) ={E2,E1}=∗
                           primitive_laws.steps_auth (S n) ∗ P))).

  Notation "|~{ E1 , E2 }~> P" := (step_update E1 E2 P) (at level 99, P at level 200, format "'[  ' |~{ E1 , E2 }~>  '/' P ']'").
  Notation "|~{ E }~> P" := (|~{E,E}~> P) (at level 99, P at level 200, format "'[  ' |~{  E  }~>  '/' P ']'").
  Notation "|~~> P" := (|~{∅}~> P) (at level 99, P at level 200, format "'[  ' |~~>  '/' P ']'").

  Lemma wp_step_update s E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (|~{E1,E2}~> P) -∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗
    WP e @ s; E1 {{ Φ }}.
  Proof.
    rewrite !wp_unfold /wp_pre /=.
    iIntros (-> HE) "HP Hwp".
    iIntros (σ1 ns κ κs m) "(Hσ & Hκ & Hsteps)".
    iMod ("HP" with "Hsteps") as "[Hsteps HP]".
    iMod ("Hwp" $! σ1 ns κ κs m with "[$Hσ $Hκ $Hsteps]") as "[%Hs Hwp]".
    iModIntro. iSplit; [done|].
    iIntros (e2 σ2 efs Hstep) "Hcred".
    iMod ("Hwp" with "[//] Hcred") as "Hwp"=> /=.
    iMod "HP".
    iIntros "!> !>". iMod "Hwp" as "Hwp". iMod "HP". iIntros "!>".
    iAssert (|={∅}▷=>^(ns) _ ∗ _)%I with "[HP Hwp]" as "Hwp".
    { iApply step_fupdN_empty_sep. iFrame. }
    iApply (step_fupdN_wand with "Hwp").
    iIntros "[Hwp H]".
    iMod "Hwp" as "(($ & $ & Hsteps) & Hwp & $)".
    iMod ("H" with "Hsteps") as "[Hsteps HP]".
    iModIntro. iFrame.
    iApply (wp_strong_mono with "Hwp"); [done|done|..].
    iIntros (v) "H". by iApply "H".
  Qed.

  Lemma step_update_frame_l E1 E2 P Q :
    (|~{E1,E2}~> P) -∗ (|={E1}=> Q) -∗ |~{E1,E2}~> (P ∗ Q).
  Proof.
    iIntros "HP HQ" (n) "Hauth".
    iMod "HQ". iMod ("HP" with "Hauth") as "[Hauth HP]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iIntros "!>!>". iMod "HP". iIntros "!>".
    iApply (step_fupdN_wand with "HP").
    iIntros "HP Hauth". iMod ("HP" with "Hauth") as "[Hauth HP]". by iFrame.
  Qed.

  (* TODO: Strenghten masks *)
  Lemma step_update_comm P Q :
    (|~~> P) -∗ (|~~> Q) -∗ |~~> P ∗ Q.
  Proof.
    iIntros "HP HQ" (n) "Hauth".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iMod ("HQ" with "Hauth") as "[Hauth HQ]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iMod "HQ". iIntros "!>!>". iMod "HP". iMod "HQ". iIntros "!>".
    iDestruct (step_fupdN_empty_sep with "[$HP $HQ]") as "HPQ".
    iApply (step_fupdN_wand with "[HPQ]"); first by iApply "HPQ".
    iIntros "[HP HQ] Hauth".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iMod ("HQ" with "Hauth") as "[Hauth HQ]".
    by iFrame.
  Qed.

  Lemma step_update_mono E1 E2 E3 P Q :
    E2 ⊆ E1 → (|~{E2,E3}~> P) -∗ (P ={E2,E1}=∗ Q) -∗ |~{E1,E3}~> Q.
  Proof.
    iIntros (Hle) "HP HPQ". iIntros (n) "Hauth".
    iApply fupd_mask_weaken; [done|]. iIntros "Hclose".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iIntros "!>!>". iMod "HP". iIntros "!>".
    iAssert (|={∅}▷=>^n _ ∗ _)%I with "[HPQ HP]" as "H".
    { iApply step_fupdN_frame_l. iFrame. iExact "HPQ". }
    iApply (step_fupdN_wand with "H").
    iIntros "[HPQ HP] Hauth".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iMod ("HPQ" with "HP") as "HQ".
    by iFrame.
  Qed.

  Lemma step_update_impl E1 E2 P Q :
    (|~{E2,E2}~> P) -∗ (|~{E1,E2}~> P -∗ Q) -∗ |~{E1,E2}~> Q.
  Proof.
    iIntros "HP HPQ" (n) "Hauth".
    iMod ("HPQ" with "Hauth") as "[Hauth HPQ]".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iMod "HPQ". iIntros "!>!>". iMod "HP". iMod "HPQ". iIntros "!>".
    iAssert (|={∅}▷=>^n _ ∗ _)%I with "[HPQ HP]" as "H".
    { iApply step_fupdN_empty_sep. iFrame. }
    iApply (step_fupdN_wand with "H").
    iIntros "[HP HPQ] Hauth".
    iMod ("HP" with "Hauth") as "[Hauth HP]".
    iMod ("HPQ" with "Hauth") as "[Hauth HPQ]".
    iFrame. by iApply "HPQ".
  Qed.

  Lemma step_update_open E1 E2 E3 P :
    (|={E1,E2}=> |~{E2,E3}~> (|={E2, E1}=> P)) -∗ |~{E1,E3}~> P.
  Proof.
    iIntros "Hstep" (n) "Hauth".
    iMod "Hstep". iMod ("Hstep" with "Hauth") as "[Hauth Hstep]".
    iIntros "!>". iFrame=> /=.
    iMod "Hstep". iIntros "!>!>". iMod "Hstep". iIntros "!>".
    iApply (step_fupdN_wand with "Hstep").
    iIntros "Hstep Hauth".
    iMod ("Hstep" with "Hauth") as "[Hauth Hstep]".
    iMod "Hstep". iModIntro. by iFrame.
  Qed.

  Lemma step_update_lb_update E n :
    steps_lb n -∗ |~{E}~> (steps_lb (S n)).
  Proof.
    iIntros "Hlb" (m) "Hauth".
    iDestruct (primitive_laws.steps_lb_valid with "Hauth Hlb") as %Hvalid.
    iApply fupd_mask_intro; [done|]. iIntros "Hclose". iFrame=> /=.
    iIntros "!>!>!>".
    iApply step_fupdN_intro; [done|].
    iIntros "!> Hauth".
    iDestruct (primitive_laws.steps_lb_get with "Hauth") as "#Hlb'".
    iDestruct (primitive_laws.steps_lb_le _ (S n) with "Hlb'") as "Hlb''"; [lia|].
    iMod "Hclose". iFrame. done.
  Qed.

  (* TODO: Strenghten masks *)
  Lemma step_update_lb_step E1 E2 P n :
    E2 ⊆ E1 → steps_lb n -∗ (|={∅}▷=>^(S n) P) -∗ |~{E1,E2}~> P.
  Proof.
    iIntros (Hle) "Hlb HP". iIntros (m) "Hauth".
    iDestruct (primitive_laws.steps_lb_valid with "Hauth Hlb") as %Hvalid.
    iApply fupd_mask_intro; [done|].
    iIntros "Hclose". iFrame.
    iApply (step_fupdN_le (S n)); [lia|done|].
    iApply (step_fupdN_wand with "HP").
    iIntros "HP Hauth".
    iMod "Hclose". by iFrame.
  Qed.

  (* Rules included to demonstrate how we can recover the original ad hoc rules *)
  Lemma wp_lb_update s n E e Φ :
    TCEq (to_val e) None →
    steps_lb n -∗
    WP e @ s; E {{ v, steps_lb (S n) ={E}=∗ Φ v }} -∗
    WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hval) "Hstep Hwp".
    iApply (wp_step_update with "[Hstep] Hwp"); [done|].
    by iApply step_update_lb_update.
  Qed.

  (* OBS: We lost some mask information. Might need to bump modality definition *)
  Lemma wp_step_fupdN_lb s n E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    steps_lb n -∗ (|={∅}▷=>^(S n) P) -∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗
    WP e @ s; E1 {{ Φ }}.
  Proof.
    iIntros (He HE) "Hlb HP Hwp".
    iApply (wp_step_update with "[Hlb HP] Hwp"); [done|].
    by iApply (step_update_lb_step with "Hlb [HP]"); [done|].
  Qed.

End with_Σ.

Notation "|~{ E1 , E2 }~> P" := (step_update E1 E2 P) (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~>  '/' P ']'").
Notation "|~{ E }~> P" := (|~{E,E}~> P) (at level 99, P at level 200, format "'[  ' |~{  E  }~>  '/' P ']'").
Notation "|~~> P" := (|~{∅}~> P) (at level 99, P at level 200, format "'[  ' |~~>  '/' P ']'").
