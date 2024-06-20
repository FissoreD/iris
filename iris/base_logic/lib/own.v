From iris.algebra Require Import functions gmap proofmode_classes.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export iprop.
From iris.prelude Require Import options.
Import uPred.

(** The class [inG Σ A] expresses that the CMRA [A] is in the list of functors
[Σ]. This class is similar to the [subG] class, but written down in terms of
individual CMRAs instead of (lists of) CMRA *functors*. This additional class is
needed because Coq is otherwise unable to solve type class constraints due to
higher-order unification problems. *)
Class inG (Σ : gFunctors) (A : cmra) := InG {
  inG_id : gid Σ;
  inG_apply := rFunctor_apply (gFunctors_lookup Σ inG_id);
  inG_prf : A = inG_apply (iPropO Σ) _;
}.
Global Arguments inG_id {_ _} _.
Global Arguments inG_apply {_ _} _ _ {_}.

(** We use the mode [-] for [Σ] since there is always a unique [Σ]. We use the
mode [!] for [A] since we can have multiple [inG]s for different [A]s, so we do
not want Coq to pick one arbitrarily. *)
Global Hint Mode inG - ! : typeclass_instances.

Lemma subG_inG Σ (F : gFunctor) : subG F Σ → inG Σ (rFunctor_apply F (iPropO Σ)).
Proof. move=> /(_ 0%fin) /= [j ->]. by exists j. Qed.

(** This tactic solves the usual obligations "subG ? Σ → {in,?}G ? Σ" *)
Ltac solve_inG :=
  (* Get all assumptions *)
  intros;
  (* Unfold the top-level xΣ. We need to support this to be a function. *)
  lazymatch goal with
  | H : subG (?xΣ _ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _) _ |- _ => try unfold xΣ in H
  | H : subG ?xΣ _ |- _ => try unfold xΣ in H
  end;
  (* Take apart subG for non-"atomic" lists *)
  repeat match goal with
         | H : subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
         end;
  (* Try to turn singleton subG into inG; but also keep the subG for typeclass
     resolution -- to keep them, we put them onto the goal. *)
  repeat match goal with
         | H : subG _ _ |- _ => move:(H); (apply subG_inG in H || clear H)
         end;
  (* Again get all assumptions and simplify the functors *)
  intros; simpl in *;
  (* We support two kinds of goals: Things convertible to inG;
     and records with inG and typeclass fields. Try to solve the
     first case. *)
  try assumption;
  (* That didn't work, now we're in for the second case. *)
  split; (assumption || by apply _).

(** * Definition of the connective [own] *)
Local Definition inG_unfold {Σ A} {i : inG Σ A} :
    inG_apply i (iPropO Σ) -n> inG_apply i (iPrePropO Σ) :=
  rFunctor_map _ (iProp_fold, iProp_unfold).
Local Definition inG_fold {Σ A} {i : inG Σ A} :
    inG_apply i (iPrePropO Σ) -n> inG_apply i (iPropO Σ) :=
  rFunctor_map _ (iProp_unfold, iProp_fold).

Local Definition iRes_singleton {Σ A} {i : inG Σ A} (γ : gname) (a : A) : iResUR Σ :=
  discrete_fun_singleton (inG_id i)
    {[ γ := inG_unfold (cmra_transport inG_prf a) ]}.
Global Instance: Params (@iRes_singleton) 4 := {}.

Local Definition own_def `{!inG Σ A} (γ : gname) (a : A) : iProp Σ :=
  uPred_ownM (iRes_singleton γ a).
Local Definition own_aux : seal (@own_def). Proof. by eexists. Qed.
Definition own := own_aux.(unseal).
Global Arguments own {Σ A _} γ a.
Local Definition own_eq : @own = @own_def := own_aux.(seal_eq).
Local Instance: Params (@own) 4 := {}.

(** * Properties about ghost ownership *)
Section global.
Context `{i : !inG Σ A}.
Implicit Types a : A.

(** ** Properties of [iRes_singleton] *)
Local Lemma inG_unfold_fold (x : inG_apply i (iPrePropO Σ)) :
  inG_unfold (inG_fold x) ≡ x.
Proof.
  rewrite /inG_unfold /inG_fold -rFunctor_map_compose -{2}[x]rFunctor_map_id.
  apply (ne_proper (rFunctor_map _)); split=> ?; apply iProp_unfold_fold.
Qed.
Local Lemma inG_fold_unfold (x : inG_apply i (iPropO Σ)) :
  inG_fold (inG_unfold x) ≡ x.
Proof.
  rewrite /inG_unfold /inG_fold -rFunctor_map_compose -{2}[x]rFunctor_map_id.
  apply (ne_proper (rFunctor_map _)); split=> ?; apply iProp_fold_unfold.
Qed.
Local Lemma inG_unfold_validN n (x : inG_apply i (iPropO Σ)) :
  ✓{n} (inG_unfold x) ↔ ✓{n} x.
Proof.
  split; [|apply (cmra_morphism_validN _)].
  move=> /(cmra_morphism_validN inG_fold). by rewrite inG_fold_unfold.
Qed.

Local Instance iRes_singleton_ne γ : NonExpansive (@iRes_singleton Σ A _ γ).
Proof. by intros n a a' Ha; apply discrete_fun_singleton_ne; rewrite Ha. Qed.
Local Lemma iRes_singleton_validI γ a : ✓ (iRes_singleton γ a) ⊢@{iPropI Σ} ✓ a.
Proof.
  rewrite /iRes_singleton.
  rewrite discrete_fun_validI (forall_elim (inG_id i)) discrete_fun_lookup_singleton.
  rewrite singleton_validI.
  trans (✓ cmra_transport inG_prf a : iProp Σ)%I; last by destruct inG_prf.
  apply valid_entails=> n. apply inG_unfold_validN.
Qed.
Local Lemma iRes_singleton_op γ a1 a2 :
  iRes_singleton γ (a1 ⋅ a2) ≡ iRes_singleton γ a1 ⋅ iRes_singleton γ a2.
Proof.
  rewrite /iRes_singleton discrete_fun_singleton_op singleton_op cmra_transport_op.
  f_equiv. apply: singletonM_proper. apply (cmra_morphism_op _).
Qed.

Local Instance iRes_singleton_discrete γ a :
  Discrete a → Discrete (iRes_singleton γ a).
Proof.
  intros ?. rewrite /iRes_singleton.
  apply discrete_fun_singleton_discrete, gmap_singleton_discrete; [apply _|].
  intros x Hx. assert (cmra_transport inG_prf a ≡ inG_fold x) as Ha.
  { apply (discrete_0 _). by rewrite -Hx inG_fold_unfold. }
  by rewrite Ha inG_unfold_fold.
Qed.
Local Instance iRes_singleton_core_id γ a :
  CoreId a → CoreId (iRes_singleton γ a).
Proof.
  intros. apply discrete_fun_singleton_core_id, gmap_singleton_core_id.
  by rewrite /CoreId -cmra_morphism_pcore core_id.
Qed.

Local Lemma later_internal_eq_iRes_singleton γ a r :
  ▷ (r ≡ iRes_singleton γ a) ⊢@{iPropI Σ}
  ◇ ∃ b r', r ≡ iRes_singleton γ b ⋅ r' ∧ ▷ (a ≡ b).
Proof.
  assert (NonExpansive (λ r : iResUR Σ, r (inG_id i) !! γ)).
  { intros n r1 r2 Hr. f_equiv. by specialize (Hr (inG_id i)). }
  rewrite (f_equivI (λ r : iResUR Σ, r (inG_id i) !! γ) r).
  rewrite {1}/iRes_singleton discrete_fun_lookup_singleton lookup_singleton.
  rewrite option_equivI. case Hb: (r (inG_id _) !! γ)=> [b|]; last first.
  { by rewrite /bi_except_0 -or_intro_l. }
  rewrite -except_0_intro.
  rewrite -(exist_intro (cmra_transport (eq_sym inG_prf) (inG_fold b))).
  rewrite -(exist_intro (discrete_fun_insert (inG_id _) (delete γ (r (inG_id i))) r)).
  apply and_intro.
  - apply equiv_internal_eq. rewrite /iRes_singleton.
    rewrite cmra_transport_trans eq_trans_sym_inv_l /=.
    intros i'. rewrite discrete_fun_lookup_op.
    destruct (decide (i' = inG_id i)) as [->|?].
    + rewrite discrete_fun_lookup_insert discrete_fun_lookup_singleton.
      intros γ'. rewrite lookup_op. destruct (decide (γ' = γ)) as [->|?].
      * by rewrite lookup_singleton lookup_delete Hb inG_unfold_fold.
      * by rewrite lookup_singleton_ne // lookup_delete_ne // left_id.
    + rewrite discrete_fun_lookup_insert_ne //.
      by rewrite discrete_fun_lookup_singleton_ne // left_id.
  - apply later_mono. rewrite (f_equivI inG_fold) inG_fold_unfold.
    apply: (internal_eq_rewrite' _ _ (λ b, a ≡ cmra_transport (eq_sym inG_prf) b)%I);
      [solve_proper|apply internal_eq_sym|].
    rewrite cmra_transport_trans eq_trans_sym_inv_r /=. apply internal_eq_refl.
Qed.

(** ** Properties of [own] *)
Global Instance own_ne γ : NonExpansive (@own Σ A _ γ).
Proof. rewrite !own_eq. solve_proper. Qed.
Global Instance own_proper γ :
  Proper ((≡) ==> (⊣⊢)) (@own Σ A _ γ) := ne_proper _.

Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ⊣⊢ own γ a1 ∗ own γ a2.
Proof. by rewrite !own_eq /own_def -ownM_op iRes_singleton_op. Qed.
Lemma own_mono γ a1 a2 : a2 ≼ a1 → own γ a1 ⊢ own γ a2.
Proof. move=> [c ->]. by rewrite own_op sep_elim_l. Qed.

Global Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (@own Σ A _ γ).
Proof. intros a1 a2. apply own_mono. Qed.

Lemma own_valid γ a : own γ a ⊢ ✓ a.
Proof. by rewrite !own_eq /own_def ownM_valid iRes_singleton_validI. Qed.
Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -∗ ✓ (a1 ⋅ a2).
Proof. apply entails_wand, wand_intro_r. by rewrite -own_op own_valid. Qed.
Lemma own_valid_3 γ a1 a2 a3 : own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
Proof. apply entails_wand. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.
Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ✓ a.
Proof. apply: bi.persistent_entails_r. apply own_valid. Qed.
Lemma own_valid_l γ a : own γ a ⊢ ✓ a ∗ own γ a.
Proof. by rewrite comm -own_valid_r. Qed.

Global Instance own_timeless γ a : Discrete a → Timeless (own γ a).
Proof. rewrite !own_eq /own_def. apply _. Qed.
Global Instance own_core_persistent γ a : CoreId a → Persistent (own γ a).
Proof. rewrite !own_eq /own_def; apply _. Qed.

Lemma later_own γ a : ▷ own γ a ⊢ ◇ ∃ b, own γ b ∧ ▷ (a ≡ b).
Proof.
  rewrite own_eq /own_def later_ownM. apply exist_elim=> r.
  assert (NonExpansive (λ r : iResUR Σ, r (inG_id i) !! γ)).
  { intros n r1 r2 Hr. f_equiv. by specialize (Hr (inG_id i)). }
  rewrite internal_eq_sym later_internal_eq_iRes_singleton.
  rewrite (except_0_intro (uPred_ownM r)) -except_0_and. f_equiv.
  rewrite and_exist_l. f_equiv=> b. rewrite and_exist_l. apply exist_elim=> r'.
  rewrite assoc. apply and_mono_l.
  etrans; [|apply ownM_mono, (cmra_included_l _ r')].
  eapply (internal_eq_rewrite' _ _ uPred_ownM _); [apply and_elim_r|].
  apply and_elim_l.
Qed.

(** ** Allocation *)
(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc_strong_dep (f : gname → A) (P : gname → Prop) :
  pred_infinite P →
  (∀ γ, P γ → ✓ (f γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ (f γ).
Proof.
  intros HPinf Hf.
  rewrite -(bupd_mono (∃ m, ⌜∃ γ, P γ ∧ m = iRes_singleton γ (f γ)⌝ ∧ uPred_ownM m)%I).
  - rewrite /bi_emp_valid (ownM_unit emp).
    apply bupd_ownM_updateP, (discrete_fun_singleton_updateP_empty _ (λ m, ∃ γ,
      m = {[ γ := inG_unfold (cmra_transport inG_prf (f γ)) ]} ∧ P γ));
      [|naive_solver].
    apply (alloc_updateP_strong_dep _ P _ (λ γ,
      inG_unfold (cmra_transport inG_prf (f γ)))); [done| |naive_solver].
    intros γ _ ?.
    by apply (cmra_morphism_valid inG_unfold), cmra_transport_valid, Hf.
  - apply exist_elim=>m; apply pure_elim_l=>-[γ [Hfresh ->]].
    by rewrite !own_eq /own_def -(exist_intro γ) pure_True // left_id.
Qed.
Lemma own_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
  (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (f γ).
Proof.
  intros Ha.
  apply (own_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (γ := fresh (G ∪ E)).
  exists γ. apply not_elem_of_union, is_fresh.
Qed.
Lemma own_alloc_dep (f : gname → A) :
  (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, own γ (f γ).
Proof.
  intros Ha. rewrite /bi_emp_valid (own_alloc_cofinite_dep f ∅) //; [].
  apply bupd_mono, exist_mono=>?. apply: sep_elim_r.
Qed.

Lemma own_alloc_strong a (P : gname → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ a.
Proof. intros HP Ha. eapply (own_alloc_strong_dep (λ _, a)); eauto. Qed.
Lemma own_alloc_cofinite a (G : gset gname) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ a.
Proof. intros Ha. eapply (own_alloc_cofinite_dep (λ _, a)); eauto. Qed.
Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, own γ a.
Proof. intros Ha. eapply (own_alloc_dep (λ _, a)); eauto. Qed.

(** ** Frame preserving updates *)
Lemma own_updateP P γ a : a ~~>: P → own γ a ⊢ |==> ∃ a', ⌜P a'⌝ ∗ own γ a'.
Proof.
  intros Hupd. rewrite !own_eq.
  rewrite -(bupd_mono (∃ m,
    ⌜ ∃ a', m = iRes_singleton γ a' ∧ P a' ⌝ ∧ uPred_ownM m)%I).
  - apply bupd_ownM_updateP, (discrete_fun_singleton_updateP _ (λ m, ∃ x,
      m = {[ γ := x ]} ∧ ∃ x',
      x = inG_unfold x' ∧ ∃ a',
      x' = cmra_transport inG_prf a' ∧ P a')); [|naive_solver].
    apply singleton_updateP', (iso_cmra_updateP' inG_fold).
    { apply inG_unfold_fold. }
    { apply (cmra_morphism_op _). }
    { apply inG_unfold_validN. }
    by apply cmra_transport_updateP'.
  - apply exist_elim=> m; apply pure_elim_l=> -[a' [-> HP]].
    rewrite -(exist_intro a'). rewrite -persistent_and_sep.
    by apply and_intro; [apply pure_intro|].
Qed.

Lemma own_update γ a a' : a ~~> a' → own γ a ⊢ |==> own γ a'.
Proof.
  intros. iIntros "?".
  iMod (own_updateP (a' =.) with "[$]") as (a'') "[-> $]".
  { by apply cmra_update_updateP. }
  done.
Qed.
Lemma own_update_2 γ a1 a2 a' :
  a1 ⋅ a2 ~~> a' → own γ a1 -∗ own γ a2 ==∗ own γ a'.
Proof. intros. apply entails_wand, wand_intro_r. rewrite -own_op. by iApply own_update. Qed.
Lemma own_update_3 γ a1 a2 a3 a' :
  a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a'.
Proof. intros. apply entails_wand. do 2 apply wand_intro_r. rewrite -!own_op. by iApply own_update. Qed.
End global.

Global Arguments own_valid {_ _} [_] _ _.
Global Arguments own_valid_2 {_ _} [_] _ _ _.
Global Arguments own_valid_3 {_ _} [_] _ _ _ _.
Global Arguments own_valid_l {_ _} [_] _ _.
Global Arguments own_valid_r {_ _} [_] _ _.
Global Arguments own_updateP {_ _} [_] _ _ _ _.
Global Arguments own_update {_ _} [_] _ _ _ _.
Global Arguments own_update_2 {_ _} [_] _ _ _ _ _.
Global Arguments own_update_3 {_ _} [_] _ _ _ _ _ _.

Lemma own_unit A `{i : !inG Σ (A:ucmra)} γ : ⊢ |==> own γ (ε:A).
Proof.
  rewrite /bi_emp_valid (ownM_unit emp) !own_eq /own_def.
  apply bupd_ownM_update, discrete_fun_singleton_update_empty.
  apply (alloc_unit_singleton_update (inG_unfold (cmra_transport inG_prf ε))).
  - apply (cmra_morphism_valid _), cmra_transport_valid, ucmra_unit_valid.
  - intros x. rewrite -(inG_unfold_fold x) -(cmra_morphism_op inG_unfold).
    f_equiv. generalize (inG_fold x)=> x'.
    destruct inG_prf=> /=. by rewrite left_id.
  - done.
Qed.

(** Big op class instances *)
Section big_op_instances.
  Context `{!inG Σ (A:ucmra)}.

  Global Instance own_cmra_sep_homomorphism γ :
    WeakMonoidHomomorphism op uPred_sep (≡) (own γ).
  Proof. split; try apply _. apply own_op. Qed.

  Lemma big_opL_own {B} γ (f : nat → B → A) (l : list B) :
    l ≠ [] →
    own γ ([^op list] k↦x ∈ l, f k x) ⊣⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute1 _). Qed.
  Lemma big_opM_own `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    m ≠ ∅ →
    own γ ([^op map] k↦x ∈ m, g k x) ⊣⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute1 _). Qed.
  Lemma big_opS_own `{Countable B} γ (g : B → A) (X : gset B) :
    X ≠ ∅ →
    own γ ([^op set] x ∈ X, g x) ⊣⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute1 _). Qed.
  Lemma big_opMS_own `{Countable B} γ (g : B → A) (X : gmultiset B) :
    X ≠ ∅ →
    own γ ([^op mset] x ∈ X, g x) ⊣⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute1 _). Qed.

  Global Instance own_cmra_sep_entails_homomorphism γ :
    MonoidHomomorphism op uPred_sep (⊢) (own γ).
  Proof.
    split; [split|]; try apply _.
    - intros. by rewrite own_op.
    - apply (affine _).
  Qed.

  Lemma big_opL_own_1 {B} γ (f : nat → B → A) (l : list B) :
    own γ ([^op list] k↦x ∈ l, f k x) ⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_own_1 `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    own γ ([^op map] k↦x ∈ m, g k x) ⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_own_1 `{Countable B} γ (g : B → A) (X : gset B) :
    own γ ([^op set] x ∈ X, g x) ⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_own_1 `{Countable B} γ (g : B → A) (X : gmultiset B) :
    own γ ([^op mset] x ∈ X, g x) ⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute _). Qed.
End big_op_instances.

(** Proofmode class instances *)
Section proofmode_instances.
  Context `{!inG Σ A}.
  Implicit Types a b : A.

  Global Instance into_sep_own γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoSep (is_op a) own_op. Qed.
  Global Instance into_and_own p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) own_op sep_and. Qed.

  Global Instance from_sep_own γ a b1 b2 :
    IsOp a b1 b2 → FromSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /FromSep -own_op -is_op. Qed.
  (* TODO: Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  (* Cost > 50 to give priority to [combine_sep_as_fractional]. *)
  Global Instance combine_sep_as_own γ a b1 b2 :
    IsOp a b1 b2 → CombineSepAs (own γ b1) (own γ b2) (own γ a) | 60.
  Proof. intros. by rewrite /CombineSepAs -own_op -is_op. Qed.
  (* TODO: Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_own γ b1 b2 :
    CombineSepGives (own γ b1) (own γ b2) (✓ (b1 ⋅ b2)).
  Proof.
    intros. rewrite /CombineSepGives -own_op own_valid.
    by apply: bi.persistently_intro.
  Qed.
  Global Instance from_and_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (own γ a) (own γ b1) (own γ b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed.
End proofmode_instances.

(*
  iProp version of a ≼ b.
  Like a ≼ b, this is not necessarily reflexive for non-unital camera.
*)
Definition uPred_cmra_included {Σ: gFunctors} {M: cmra} (a b : M) : iProp Σ := ∃ c , b ≡ a ⋅ c.
Infix "≼" := uPred_cmra_included (at level 70) : bi_scope.
Notation "(≼)" := uPred_cmra_included (only parsing) : bi_scope.

Section and_own_cmra.
  Context {Σ: gFunctors}.
  Context `{i : !inG Σ A}.

  (* Our main goal is to prove:
      (own γ x ∧ own γ y) ⊢
          ∃ z , own γ z
          ∧ Some x ≼ Some z
          ∧ Some y ≼ Some z
    We start by proving the analogue in the global ucmra, using uPred_ownM.
  *)

  Local Lemma uPred_ownM_and (x y : iResUR Σ) :
    (uPred_ownM x ∧ uPred_ownM y) ⊢ ∃ z , uPred_ownM z ∧ x ≼ z ∧ y ≼ z.
  Proof.
    uPred.unseal. split. intros n w val_w lhs.
    unfold upred.uPred_and_def in lhs. unfold uPred_holds in lhs.
    unfold upred.uPred_ownM_def in lhs. destruct lhs as [x_incl_w y_incl_w].
    unfold upred.uPred_exist_def. unfold uPred_holds. exists w.
    unfold upred.uPred_and_def. split.
    { unfold uPred_holds. unfold upred.uPred_ownM_def. trivial. }
    unfold uPred_holds. unfold uPred_cmra_included.
    uPred.unseal. unfold upred.uPred_internal_eq_def. unfold uPred_holds. split.
    { unfold includedN in x_incl_w. trivial. }
    { unfold includedN in x_incl_w. trivial. }
  Qed.

  (* Now, we need to relate `uPred_ownM (iRes_singleton γ _)` to `own γ _` so that we
    can bring this theorem from the global ucmra world to the A world.
    In particular, uPred_ownM_and gives us some `z` in the ucmra world, but to prove
    the theorem in the end, we need a `z` in the A world.
    We start by defining this `project` function to map from the ucmra world to the A world:
  *)

  Local Definition project (x : iResUR Σ) (γ : gname) : option A :=
    match (x (inG_id i) !! γ) with
    | Some t => Some (cmra_transport (eq_sym inG_prf) (inG_fold t))
    | None => None
    end.

  (* Now we prove some nice properties about `project` *)

  Local Lemma project_op (x y : iResUR Σ) γ n :
    (project (x ⋅ y) γ : option A) ≡{n}≡ (project x γ ⋅ project y γ).
  Proof.
    unfold project. rewrite lookup_op.
    destruct (x (inG_id i) !! γ) as [x1|] eqn:p1; destruct (y (inG_id i) !! γ) as [y1|] eqn:p2.
    - rewrite p1. rewrite p2.
        replace (Some x1 ⋅ Some y1) with (Some (x1 ⋅ y1)) by trivial.
        enough (cmra_transport (eq_sym inG_prf) (inG_fold (x1 ⋅ y1)) ≡{n}≡ 
                cmra_transport (eq_sym inG_prf) (inG_fold x1)
                ⋅ cmra_transport (eq_sym inG_prf) (inG_fold y1)) as H.
        { intros. setoid_rewrite H. trivial. }
        setoid_rewrite <- cmra_transport_op. f_equiv.
        unfold inG_fold. apply equiv_dist. apply cmra_morphism_op. typeclasses eauto.
    - rewrite p1. rewrite p2. trivial.
    - rewrite p1. rewrite p2. trivial.
    - rewrite p1. rewrite p2. trivial.
  Qed.

  Local Instance proper_project_equiv_n (n : nat) : Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡)) project.
  Proof.
    unfold Proper, "==>". intros x y H γ γ0 s0. unfold project. subst γ0.
    assert (x (inG_id i) !! γ ≡{n}≡ y (inG_id i) !! γ) as M.
    { enough (x (inG_id i) ≡{n}≡ y (inG_id i)). { trivial. } trivial. }
    destruct (x (inG_id i) !! γ) as [x1|]; destruct (y (inG_id i) !! γ) as [y1|].
    - assert (x1 ≡{n}≡ y1) as Q.
      + unfold "≡" in M. unfold ofe_equiv, optionO, option_equiv in M. inversion M. trivial.
      + setoid_rewrite Q. trivial.
    - inversion M.
    - inversion M.
    - trivial.
  Qed.

  Local Lemma project_iRes_singleton (x : A) (γ : gname) :
    project (iRes_singleton γ x) γ ≡ Some x.
  Proof.
    unfold project, iRes_singleton. setoid_rewrite discrete_fun_lookup_singleton.
    rewrite lookup_singleton. f_equiv. setoid_rewrite inG_fold_unfold.
    rewrite cmra_transport_trans eq_trans_sym_inv_r /=. trivial.
  Qed.

  (* 
    To get from,
      ∃ z ,  uPred_ownM z   ∧ x ≼ z    ∧ y ≼ z
    to,
      ∃ z' , own γ z'       ∧ x ≼ z'   ∧ y ≼ z'
    We're going to set z' to be the projection of z. This requires us to establish
    3 entailments. The next lemma handles the first one, `uPred_ownM z ⊢ own γ z`:
  *)

  Local Lemma iRes_incl_from_proj γ z' z n :
    project z γ = Some z' →
        iRes_singleton γ z' ≼{n} z.
  Proof.
    intro p. unfold project in p. destruct (z (inG_id i) !! γ) as [z1|] eqn:e.
    - assert ((cmra_transport (eq_sym inG_prf) (inG_fold z1)) ≡ z') as X.
      { unfold "≡", ofe_equiv, optionO, option_equiv in p. inversion p. trivial. }
      unfold includedN. unfold iRes_singleton.
      exists (discrete_fun_insert (inG_id i) (delete γ (z (inG_id i))) z).
      apply equiv_dist. intros x'.
      have h : Decision (inG_id i = x') by solve_decision. destruct h.
      + setoid_rewrite discrete_fun_lookup_op. subst x'.
        setoid_rewrite discrete_fun_lookup_singleton.
        setoid_rewrite discrete_fun_lookup_insert.
        intro γ0.
        have h1 : Decision (γ = γ0) by solve_decision. destruct h1.
        * subst γ0. rewrite lookup_op. rewrite lookup_delete.
          rewrite lookup_singleton. rewrite e.
          unfold "⋅", cmra_op, optionR, option_op_instance, union_with, option_union_with.
          f_equiv. setoid_rewrite <- X.
          rewrite cmra_transport_trans eq_trans_sym_inv_l /=.
          setoid_rewrite inG_unfold_fold. trivial.
        * rewrite lookup_op. rewrite lookup_delete_ne; trivial.
          rewrite lookup_singleton_ne; trivial.
          unfold "⋅", cmra_op, optionR, option_op_instance, union_with, option_union_with.
          destruct (z (inG_id i) !! γ0) eqn:s.
          ++ rewrite s. trivial.
          ++ rewrite s. trivial.
      + setoid_rewrite discrete_fun_lookup_op.
        setoid_rewrite discrete_fun_lookup_singleton_ne; trivial.
        setoid_rewrite discrete_fun_lookup_insert_ne; trivial.
        symmetry. apply ucmra_unit_left_id.
    - inversion p.
  Qed.

  Local Lemma uPred_ownM_implies_project_at_γ γ z' z :
    project z γ = Some z' → uPred_ownM z ⊢ uPred_ownM (iRes_singleton γ z').
  Proof.
    intros proj_eq. split. intros n t val_t.
    rewrite upred.uPred_ownM_unseal. unfold uPred_holds. unfold upred.uPred_ownM_def.
    intros w_le_t. have own_le_w := iRes_incl_from_proj γ z' z n proj_eq.
    eapply cmra_includedN_trans. { apply own_le_w. } trivial.
  Qed.

  (* This handles the other two entailments: *)

  Local Lemma uPred_ucmra_incl_implies_incl_at_γ γ x z' z :
      project z γ = Some z' →
        iRes_singleton γ x ≼ z ⊢ 
            @uPred_cmra_included Σ (option A) (Some x) (Some z').
  Proof.
    intros proj_eqn. unfold uPred_cmra_included.
    uPred.unseal. split. intros n x0 val_x0 uh.
    unfold upred.uPred_exist_def, uPred_holds in uh.
    unfold upred.uPred_internal_eq_def in uh.
    unfold uPred_holds, upred.uPred_exist_def.
    unfold upred.uPred_internal_eq_def, uPred_holds.
    destruct uh as [c uh]. exists (project c γ).
    assert (project z γ ≡{n}≡ project (iRes_singleton γ x) γ ⋅ project c γ) as X.
      { setoid_rewrite <- project_op. setoid_rewrite <- uh. trivial. }
    setoid_rewrite project_iRes_singleton in X.
    rewrite proj_eqn in X. unfold "⋅?". destruct (project c γ).
    - inversion X. trivial.
    - inversion X. trivial.
  Qed.

  (* We also need to show the projection is not None.
      TODO: some duplication with the above *)

  Local Lemma uPred_ucmra_incl_projection_is_not_none γ (x : A) (z : iResUR Σ)
    : project z γ = None →
        @uPred_cmra_included Σ (iResUR Σ) (iRes_singleton γ x) z ⊢ False.
  Proof.
    intros proj_eqn. unfold uPred_cmra_included.
    uPred.unseal. split. intros n x0 val_x0 uh.
    unfold upred.uPred_exist_def, uPred_holds in uh.
    unfold upred.uPred_internal_eq_def in uh.
    exfalso. destruct uh as [c uh].
    assert (project z γ ≡{n}≡ project (iRes_singleton γ x) γ ⋅ project c γ) as X.
      { setoid_rewrite <- project_op. setoid_rewrite <- uh. trivial. }
    setoid_rewrite project_iRes_singleton in X.
    rewrite proj_eqn in X. unfold "⋅?". destruct (project c γ).
    - inversion X.
    - inversion X.
  Qed.

  (* Finally we tie it all together. *)

  Lemma and_own (γ : gname) (x y : A) :
    (own γ x ∧ own γ y) ⊢ ∃ z , own γ z
        ∗ Some x ≼ Some z
        ∗ Some y ≼ Some z.
  Proof.
    rewrite own_eq. unfold own_def. iIntros "and_own".
    iDestruct (uPred_ownM_and with "and_own") as (z) "[own_z [x_le_z y_le_z]]".
    destruct (project z γ) as [z'|] eqn:proj_eqn.
    { 
      iExists z'. iSplitL "own_z".
      { iApply (uPred_ownM_implies_project_at_γ γ z' z); trivial. }
      iSplitL "x_le_z".
      { iApply (uPred_ucmra_incl_implies_incl_at_γ γ x z' z); trivial. }
      { iApply (uPred_ucmra_incl_implies_incl_at_γ γ y z' z); trivial. }
    }
    { iExFalso. iApply (uPred_ucmra_incl_projection_is_not_none γ x z); trivial. }
  Qed.

  (* Now some corollaries *)

  Local Lemma uPred_cmra_incl_discrete_implies_pure {D : CmraDiscrete A} (x y : A) :
    @uPred_cmra_included Σ (option A) (Some x) (Some y)  ⊢ ⌜ Some x ≼ Some y ⌝.
  Proof.
    unfold uPred_cmra_included. iIntros "eq". iDestruct "eq" as (c) "eq".
    iDestruct (discrete_eq_1 with "eq") as "%Heq".
    unfold "≼". iPureIntro. exists c. trivial.
  Qed.

  Lemma and_own_discrete {D : CmraDiscrete A} (γ : gname) (x y : A) :
    (own γ x ∧ own γ y) ⊢ ∃ z , own γ z ∗ ⌜ Some x ≼ Some z ∧ Some y ≼ Some z ⌝.
  Proof.
    iIntros "and_own". iDestruct (and_own with "and_own") as (z) "[own [a b]]".
    iExists z. iFrame "own".
    iDestruct (uPred_cmra_incl_discrete_implies_pure with "a") as "%a".
    iDestruct (uPred_cmra_incl_discrete_implies_pure with "b") as "%b".
    iPureIntro; split; trivial.
  Qed.
End and_own_cmra.

Section and_own_ucmra.
  Context {Σ : gFunctors}.
  Context {A : ucmra}.
  Context `{i : !inG Σ A}.

  Local Lemma uPred_cmra_incl_ucmra_discrete_implies_pure {D : CmraDiscrete A} (x y : A) :
    @uPred_cmra_included Σ (option A) (Some x) (Some y)  ⊢ ⌜ x ≼ y ⌝.
  Proof.
    unfold uPred_cmra_included. iIntros "eq". iDestruct "eq" as (c) "eq".
    iDestruct (discrete_eq_1 with "eq") as "%eq". unfold "≼". iPureIntro. destruct c as [c|].
    - exists c. setoid_rewrite <- Some_op in eq. inversion eq. trivial.
    - exists ε. rewrite right_id. inversion eq. trivial.
  Qed.

  Lemma and_own_discrete_ucmra {D : CmraDiscrete A} (γ : gname) (x y : A) :
    (own γ x ∧ own γ y) ⊢ ∃ z , own γ z ∗ ⌜ x ≼ z ∧ y ≼ z ⌝.
  Proof.
    iIntros "and_own". iDestruct (and_own with "and_own") as (z) "[own [a b]]".
    iExists z. iFrame "own".
    iDestruct (uPred_cmra_incl_ucmra_discrete_implies_pure with "a") as "%a".
    iDestruct (uPred_cmra_incl_ucmra_discrete_implies_pure with "b") as "%b".
    iPureIntro; split; trivial.
  Qed.

  Lemma and_own_discrete_ucmra_specific {D : CmraDiscrete A} (γ : gname) (x y z : A) :
    (∀ w , ✓ w → x ≼ w → y ≼ w → z ≼ w) →
    (own γ x ∧ own γ y) ⊢ own γ z.
  Proof.
    intros Hw. iIntros "and_own".
    iDestruct (and_own_discrete_ucmra with "and_own") as (w) "[own [%Hx %Hy]]".
    iDestruct (own_valid with "own") as "%Hv".
    assert (z ≼ w) as z_le_w. { apply Hw; trivial. }
    unfold "≼" in z_le_w. destruct z_le_w as [z1 eq]. setoid_rewrite eq.
    iDestruct "own" as "[own1 own2]". iFrame.
  Qed.

  Lemma and_own_discrete_ucmra_contradiction {D : CmraDiscrete A} (γ : gname) (x y : A) :
    (∀ w , ✓ w → x ≼ w → y ≼ w → False) →
    (own γ x ∧ own γ y) ⊢ False.
  Proof.
    intros Hw. iIntros "and_own".
    iDestruct (and_own_discrete_ucmra with "and_own") as (w) "[own [%Hx %Hy]]".
    iDestruct (own_valid with "own") as "%Hv". exfalso. apply (Hw w); trivial.
  Qed.
End and_own_ucmra.
