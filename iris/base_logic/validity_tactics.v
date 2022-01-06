From iris.algebra Require Import cmra proofmode_classes auth frac_auth.
From iris.proofmode Require Import proofmode environments.
From iris.base_logic Require Import own proofmode_classes proofmode_instances.
From iris.prelude Require Import options.

(* base lemmas to use the validity typeclasses *)

Lemma own_valid_op {A : cmra} (a a1 a2 : A) γ `{!inG Σ A} (P : iProp Σ) :
  IsValidOp _ a a1 a2 P →
  own γ a1 -∗ own γ a2 -∗ own γ a ∗ □ P.
Proof.
  case => HP Ha.
  iIntros "Ha1 Ha2".
  iAssert (✓ (a1 ⋅ a2))%I as "#H✓".
  { iApply (own_valid_2 with "Ha1 Ha2"). }
  iSplit; last by iApply HP.
  iAssert (a ≡ a1 ⋅ a2)%I with "[Ha1 Ha2]" as "#Heq"; first by iApply Ha.
  iRewrite "Heq".
  rewrite own_op; iFrame.
Qed.

Lemma is_included_auth {A : ucmra} (a1 a2 : A) dq γ `{!inG Σ $ authUR A} (P : iProp Σ) :
  IsIncluded _ a1 a2 P →
  own γ (●{dq} a2) -∗ own γ (◯ a1) -∗ □ P.
Proof.
  rewrite /IsIncluded => HP.
  iIntros "Ha1 Ha2".
  iCombine "Ha1 Ha2" as "Ha".
  rewrite own_valid auth_both_dfrac_validI.
  iDestruct "Ha" as "(_ & [%c #Hc] & #H✓)".
  iApply (HP with "H✓").
  iExists c. iApply "Hc".
Qed.


(* now their coq tactic variants, for applying them to IPM proofs *)

Lemma tac_own_valid_op {A : cmra} i1 i2 (a a1 a2 : A) p1 p2 γ `{!inG Σ A} (P G : iProp Σ) Δ :
  envs_lookup i1 Δ = Some (p1, own γ a1) →
  envs_lookup i2 (envs_delete true i1 p1 Δ) = Some (p2, own γ a2) →
  IsValidOp _ a a1 a2 P →
  envs_entails (envs_delete true i2 p2 (envs_delete true i1 p1 Δ)) ((own γ a ∗ □ P) -∗ G)%I →
  envs_entails Δ G.
Proof.
  rewrite envs_entails_eq => Hi1 Hi2 HaP HΔ.
  erewrite envs_lookup_sound => //.
  erewrite envs_lookup_sound => //.
  rewrite !bi.intuitionistically_if_elim HΔ.
  iIntros "(Ha1 & Ha2 & HaPG)".
  iApply "HaPG".
  case: HaP => <- HaP.
  iDestruct (own_valid_2 with "Ha1 Ha2") as "#H✓".
  iFrame "#".
  rewrite HaP.
  iRewrite "H✓".
  by iCombine "Ha1 Ha2" as "$".
Qed.

Lemma tac_auth_included {A : ucmra} i1 i2 (a1 a2 : A) dq p1 p2 γ `{!inG Σ $ authUR A} (P G : iProp Σ) Δ :
  envs_lookup i1 Δ = Some (p1, own γ (●{dq} a1)) →
  envs_lookup i2 (envs_delete true i1 p1 Δ) = Some (p2, own γ (◯ a2)) →
  IsIncluded _ a2 a1 P →
  envs_entails Δ (□ P -∗ G)%I →
  envs_entails Δ G.
Proof.
  rewrite envs_entails_eq => Hi1 Hi2 HaP HΔ.
  iIntros "HΔ".
  iAssert (□ P)%I as "#HP".
  { erewrite envs_lookup_sound => //.
    erewrite envs_lookup_sound => //.
    rewrite !bi.intuitionistically_if_elim.
    iDestruct "HΔ" as "(Ha1 & Ha2 & _)".
    iApply (is_included_auth with "Ha1 Ha2") => //. }
  iApply (HΔ with "HΔ") => //.
Qed.


Ltac iCombineOwn_tac' Hs_raw destructstr := 
  let Hs := words Hs_raw in
  let get_hyp_type Hname := 
    let Δ := match goal with | |- environments.envs_entails ?Δ _ => Δ end in
    let lookup := eval pm_eval in (environments.envs_lookup (INamed Hname) Δ) in
    match lookup with
    | Some (_, ?Htype) => constr:(Htype)
    end
  in
  first
  [ match Hs with
    | ?H0n :: ?H1n :: nil =>
      let H0 := get_hyp_type H0n in
      let H1 := get_hyp_type H1n in
      let pr := constr:((H0, H1)) in
      first 
      [
(*      lazymatch pr with
      | (*(own ?γ (● _), own ?γ (◯ _)) => *) *)
          eapply (tac_auth_included (INamed H0n) (INamed H1n));
          [ reflexivity| reflexivity| iSolveTC | ];
          iIntros destructstr
      | (*(own ?γ (◯ _), own ?γ (● _)) => *)
          eapply (tac_auth_included (INamed H1n) (INamed H0n));
          [ reflexivity| reflexivity| iSolveTC | ];
          iIntros destructstr
      | (*_ => *)
          let tempname := iFresh in
          iDestruct (own_valid_op with Hs_raw) as tempname;
          iDestruct tempname as destructstr
      | fail 4 "Could not find validity lemma for "H0 "and" H1
      (*end*) ]
    end
  | (fail 2 "Expected exactly two hypothesis, got" Hs_raw)].

Tactic Notation "iCombineOwn" constr(hypstr) "as" constr(destructstr) :=
  iCombineOwn_tac' hypstr destructstr.