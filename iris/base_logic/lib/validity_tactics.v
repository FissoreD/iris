From iris.algebra Require Import cmra proofmode_classes auth frac_auth.
From iris.proofmode Require Import proofmode environments.
From iris.base_logic.lib Require Import own proofmode_classes proofmode_instances.
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

Lemma own_valid_gives {A : cmra} (a1 a2 : A) γ `{!inG Σ A} (P : iProp Σ) :
  IsValidGives _ a1 a2 P →
  own γ a1 -∗ own γ a2 -∗ □ P.
Proof.
  rewrite /IsValidGives => HaP.
  rewrite own_valid_2. apply bi.wand_intro_r.
  by erewrite bi.wand_elim_l.
Qed.


(* now their coq tactic variants, for applying them to IPM proofs *)

Lemma tac_own_valid_op i1 i2 {A : cmra} (a a1 a2 : A) p1 p2 γ `{!inG Σ A} (P G : iProp Σ) Δ :
  envs_lookup i1 Δ = Some (p1, own γ a1) →
  envs_lookup i2 (envs_delete true i1 p1 Δ) = Some (p2, own γ a2) →
  IsValidOp _ a a1 a2 P →
  envs_entails (envs_delete true i2 p2 (envs_delete true i1 p1 Δ)) (own γ a -∗ P -∗ G)%I →
  envs_entails Δ G.
Proof.
  rewrite envs_entails_eq => Hi1 Hi2 HaP HΔ.
  erewrite envs_lookup_sound => //.
  erewrite envs_lookup_sound => //.
  rewrite !bi.intuitionistically_if_elim HΔ.
  iIntros "(Ha1 & Ha2 & HaPG)".
  iDestruct (own_valid_2 with "Ha1 Ha2") as "#H✓".
  iApply ("HaPG" with "[Ha1 Ha2]").
  - case: HaP => _ HaP.
    rewrite HaP.
    iRewrite "H✓".
    by iCombine "Ha1 Ha2" as "$".
  - rewrite is_valid_gives //.
Qed.

Lemma tac_own_valid_gives i1 i2 {A : cmra} (a1 a2 : A) p1 p2 γ `{!inG Σ A} (P G : iProp Σ) Δ :
  envs_lookup i1 Δ = Some (p1, own γ a1) →
  envs_lookup i2 (envs_delete true i1 p1 Δ) = Some (p2, own γ a2) →
  IsValidGives _ a1 a2 P →
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
    iCombine "Ha1 Ha2" as "Ha".
    rewrite own_valid is_valid_gives //. }
  iApply (HΔ with "HΔ") => //.
Qed.


Ltac iCombineOwn_gen_pre Hs_raw lem := 
  let Hs := words Hs_raw in
  let get_hyp_type Hname := 
    let Δ := match goal with | |- environments.envs_entails ?Δ _ => Δ end in
    let lookup := eval pm_eval in (environments.envs_lookup (INamed Hname) Δ) in
    match lookup with
    | Some (_, ?Htype) => constr:(Htype)
    end
  in
  first
  [ lazymatch Hs with
    | ?H0n :: ?H1n :: nil => 
      let H0 := get_hyp_type H0n in (* this may fail if the supplied hypname is not present *)
      let H1 := get_hyp_type H1n in
      eapply (lem (INamed H0n) (INamed H1n)); 
      [ first [reflexivity | fail 2 "Failed to turn"H0"into an own"]
      | first [reflexivity | fail 2 "Failed to turn"H1"into an own"]
      | lazymatch goal with
        | |- proofmode_classes.IsValidOp _ _ ?a1 ?a2 _ =>
          first [iSolveTC | fail 2 "Did not find a simplification of"a1"⋅"a2 ]
        | |- proofmode_classes.IsValidGives _ ?a1 ?a2 _ =>
          first [iSolveTC | fail 2 "Did not find a consequence of the validity of"a1"⋅"a2 ]
        end
      | reduction.pm_reduce ] (* simplify the envs_delete *)
    | _ => (fail 1 "Expected exactly two hypothesis, got" Hs_raw)
    end
  | fail 1 "One of the supplied hypothesis in"Hs_raw"does not exist" ].


Ltac iCombineOwn_op_pre Hs_raw :=
  iCombineOwn_gen_pre Hs_raw (@tac_own_valid_op).

Ltac iCombineOwn_gives_pre Hs_raw :=
  iCombineOwn_gen_pre Hs_raw (@tac_own_valid_gives).



Tactic Notation "iCombineOwn" constr(hyppat) "as" constr(newoppat) "gives" constr(validpat) :=
  iCombineOwn_op_pre hyppat;
  iDestruct 1 as newoppat;
  iDestruct 1 as validpat.

Tactic Notation "iCombineOwn" constr(hyppat) "as" constr(newoppat) "gives" "%" simple_intropattern(validpat) :=
  iCombineOwn_op_pre hyppat;
  iDestruct 1 as newoppat;
  iDestruct 1 as %validpat.

Tactic Notation "iCombineOwn" constr(hyppat) "gives" constr(validpat) :=
  iCombineOwn_gives_pre hyppat;
  iDestruct 1 as validpat.

Tactic Notation "iCombineOwn" constr(hyppat) "gives" "%" simple_intropattern(validpat) :=
  iCombineOwn_gives_pre hyppat;
  iDestruct 1 as %validpat.



























