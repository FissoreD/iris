From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export derived_laws.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Local Open Scope Z_scope.

(** Provides some array utilities:

* [array_free], to deallocate an entire array in one go.
* [array_copy_to], a function which copies to an array in-place.
* Using [array_copy_to] we also implement [array_clone], which allocates a fresh
array and copies to it.
* [array_init], to create and initialize an array with a given
function. Specifically, [array_init n f] creates a new array of size
[n] in which the [i]th element is initialized with [f #i]

*)

Definition array_free : val :=
  rec: "freeN" "ptr" "n" :=
    if: "n" ≤ #0 then #()
    else Free "ptr";;
         "freeN" ("ptr" +ₗ #1) ("n" - #1).

Definition array_copy_to : val :=
  rec: "array_copy_to" "dst" "src" "n" :=
    if: "n" ≤ #0 then #()
    else "dst" <- !"src";;
         "array_copy_to" ("dst" +ₗ #1) ("src" +ₗ #1) ("n" - #1).

Definition array_clone : val :=
  λ: "src" "n",
    let: "dst" := AllocN "n" #() in
    array_copy_to "dst" "src" "n";;
    "dst".

(* [array_init_loop src i n f] initializes elements
   [i], [i+1], ..., [n] of the array [src] to
   [f #i], [f #(i+1)], ..., [f #n] *)
Local Definition array_init_loop : val :=
  rec: "loop" "src" "i" "n" "f" :=
    if: "i" = "n" then #()
    else "src" +ₗ "i" <- "f" "i";;
         "loop" "src" ("i" + #1) "n" "f".

Definition array_init : val :=
  λ: "n" "f",
    let: "src" := AllocN "n" #() in
    array_init_loop "src" #0 "n" "f";;
    "src".

Section proof.
  Context `{!heapGS_gen hlc Σ}.

  Lemma twp_array_free s E l vs (n : Z) :
    n = lengthZ vs →
    [[{ l ↦∗ vs }]] array_free #l #n @ s; E [[{ RET #(); True }]].
  Proof.
    iIntros (Hlen Φ) "Hl HΦ".
    iInduction vs as [|v vs] "IH" forall (l n Hlen); subst n; wp_rec; wp_pures.
    { iApply "HΦ". done. }
    iDestruct (array_cons with "Hl") as "[Hv Hl]". rewrite cons_lengthZ.
    wp_free. wp_pures. iApply ("IH" with "[] Hl"); eauto with lia.
  Qed.
  Lemma wp_array_free s E l vs (n : Z) :
    n = lengthZ vs →
    {{{ l ↦∗ vs }}} array_free #l #n @ s; E {{{ RET #(); True }}}.
  Proof.
    iIntros (? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_free with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.

  Lemma twp_array_copy_to stk E (dst src : loc) vdst vsrc dq (n : Z) :
    lengthZ vdst = n → lengthZ vsrc = n →
    [[{ dst ↦∗ vdst ∗ src ↦∗{dq} vsrc }]]
      array_copy_to #dst #src #n @ stk; E
    [[{ RET #(); dst ↦∗ vsrc ∗ src ↦∗{dq} vsrc }]].
  Proof.
    iIntros (Hvdst Hvsrc Φ) "[Hdst Hsrc] HΦ".
    iInduction vdst as [|v1 vdst] "IH" forall (n dst src vsrc Hvdst Hvsrc);
      destruct vsrc as [|v2 vsrc]; simplify_eq/=; try lia; wp_rec; wp_pures.
    { iApply "HΦ". auto with iFrame. }
    iDestruct (array_cons with "Hdst") as "[Hv1 Hdst]".
    iDestruct (array_cons with "Hsrc") as "[Hv2 Hsrc]".
    wp_load; wp_store. rewrite cons_lengthZ.
    wp_smart_apply ("IH" with "[%] [%] Hdst Hsrc"); [ lia .. | ].
    iIntros "[Hvdst Hvsrc]".
    iApply "HΦ"; by iFrame.
  Qed.
  Lemma wp_array_copy_to stk E (dst src : loc) vdst vsrc dq (n : Z) :
    lengthZ vdst = n → lengthZ vsrc = n →
    {{{ dst ↦∗ vdst ∗ src ↦∗{dq} vsrc }}}
      array_copy_to #dst #src #n @ stk; E
    {{{ RET #(); dst ↦∗ vsrc ∗ src ↦∗{dq} vsrc }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_copy_to with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.

  Lemma twp_array_clone stk E l dq vl n :
    lengthZ vl = n →
    (0 < n)%Z →
    [[{ l ↦∗{dq} vl }]]
      array_clone #l #n @ stk; E
    [[{ l', RET #l'; l' ↦∗ vl ∗ l ↦∗{dq} vl }]].
  Proof.
    iIntros (Hvl Hn Φ) "Hvl HΦ".
    wp_lam.
    wp_alloc dst as "Hdst"; first by auto.
    wp_smart_apply (twp_array_copy_to with "[$Hdst $Hvl]").
    - rewrite replicateZ_lengthZ; lia.
    - auto.
    - iIntros "[Hdst Hl]".
      wp_pures.
      iApply "HΦ"; by iFrame.
  Qed.
  Lemma wp_array_clone stk E l dq vl n :
    lengthZ vl = n →
    (0 < n)%Z →
    {{{ l ↦∗{dq} vl }}}
      array_clone #l #n @ stk; E
    {{{ l', RET #l'; l' ↦∗ vl ∗ l ↦∗{dq} vl }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_clone with "H"); [auto..|]; iIntros (l') "H HΦ". by iApply "HΦ".
  Qed.

  Section array_init.
    Context (Q : Z → val → iProp Σ).
    Implicit Types (f v : val).

    Local Lemma wp_array_init_loop stk E l i n k f  :
      n = i + Z.of_nat k →
      {{{
        (l +ₗ i) ↦∗ replicate k #() ∗
        [∗ list] (j:Z) ∈ seqZ i (Z.of_nat k), WP f #j @ stk; E {{ Q j }}
      }}}
        array_init_loop #l #i #n f @ stk; E
      {{{ vs, RET #();
        ⌜ length vs = k ⌝ ∗ (l +ₗ i) ↦∗ vs ∗ [∗ listZ] j↦v ∈ vs, Q (i + j) v
      }}}.
    Proof.
      iIntros (Hn Φ) "[Hl Hf] HΦ".
      iInduction k as [|k] "IH" forall (i Hn); simplify_eq/=; wp_rec; wp_pures.
      { rewrite bool_decide_eq_true_2; last (repeat f_equal; lia).
        wp_pures. iApply ("HΦ" $! []). auto. }
      rewrite bool_decide_eq_false_2; last naive_solver lia.
      iDestruct (array_cons with "Hl") as "[Hl HSl]".
      rewrite Nat2Z.inj_succ seqZ_succ; last by lia.
      iDestruct "Hf" as "[Hf HSf]".
      wp_smart_apply (wp_wand with "Hf"); iIntros (v) "Hv". wp_store. wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      iApply ("IH" with "[%] [HSl] HSf"); first lia.
      { by rewrite loc_add_assoc Z.add_1_r. }
      iIntros "!>" (vs). iDestruct 1 as (<-) "[HSl Hvs]".
      iApply ("HΦ" $! (v :: vs)). iSplit; [naive_solver|]. iSplitL "Hl HSl".
      - iFrame "Hl". by rewrite loc_add_assoc Z.add_1_r.
      - rewrite big_sepLZ_cons. rewrite Z.add_0_r. iFrame.
        setoid_rewrite Z.add_succ_comm. iFrame.
    Qed.
    Local Lemma twp_array_init_loop stk E l i n k f  :
      n = i + Z.of_nat k →
      [[{
        (l +ₗ i) ↦∗ replicate k #() ∗
        [∗ list] (j:Z) ∈ seqZ i (Z.of_nat k), WP f #j @ stk; E [{ Q j }]
      }]]
        array_init_loop #l #i #n f @ stk; E
      [[{ vs, RET #();
        ⌜ length vs = k ⌝ ∗ (l +ₗ i) ↦∗ vs ∗ [∗ listZ] j↦v ∈ vs, Q (i + j) v
      }]].
    Proof.
      iIntros (Hn Φ) "[Hl Hf] HΦ".
      iInduction k as [|k] "IH" forall (i Hn); simplify_eq/=; wp_rec; wp_pures.
      { rewrite bool_decide_eq_true_2; last (repeat f_equal; lia).
        wp_pures. iApply ("HΦ" $! []). auto. }
      rewrite bool_decide_eq_false_2; last naive_solver lia.
      iDestruct (array_cons with "Hl") as "[Hl HSl]".
      rewrite Nat2Z.inj_succ seqZ_succ; last by lia.
      iDestruct "Hf" as "[Hf HSf]".
      wp_smart_apply (twp_wand with "Hf"); iIntros (v) "Hv". wp_store. wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      iApply ("IH" with "[%] [HSl] HSf"); first lia.
      { by rewrite loc_add_assoc Z.add_1_r. }
      iIntros (vs). iDestruct 1 as (<-) "[HSl Hvs]".
      iApply ("HΦ" $! (v :: vs)). iSplit; [naive_solver|]. iSplitL "Hl HSl".
      - iFrame "Hl". by rewrite loc_add_assoc Z.add_1_r.
      - rewrite big_sepLZ_cons. rewrite Z.add_0_r. iFrame.
        setoid_rewrite Z.add_succ_comm. iFrame.
    Qed.

    Lemma wp_array_init stk E n f :
      (0 < n)%Z →
      {{{
        [∗ list] (i:Z) ∈ seqZ 0 n, WP f #i @ stk; E {{ Q i }}
      }}}
        array_init #n f @ stk; E
      {{{ l vs, RET #l;
        ⌜lengthZ vs = n⌝ ∗ l ↦∗ vs ∗ [∗ listZ] k↦v ∈ vs, Q k v
      }}}.
    Proof.
      iIntros (Hn Φ) "Hf HΦ". wp_lam. wp_alloc l as "Hl"; first done.
      wp_smart_apply (wp_array_init_loop _ _ _ 0 n (Z.to_nat n) with "[Hl Hf] [HΦ]").
      { by rewrite /= Z2Nat.id; last lia. }
      { rewrite loc_add_0 Z2Nat.id; last lia. iFrame. }
      iIntros "!>" (vs). iDestruct 1 as (Hlen) "[Hl Hvs]". wp_pures.
      iApply ("HΦ" $! _ vs). iModIntro. iSplit.
      { iPureIntro. lia. }
      rewrite loc_add_0. iFrame.
    Qed.
    Lemma twp_array_init stk E n f :
      (0 < n)%Z →
      [[{
        [∗ list] (i:Z) ∈ seqZ 0 n, WP f #i @ stk; E [{ Q i }]
      }]]
        array_init #n f @ stk; E
      [[{ l vs, RET #l;
        ⌜lengthZ vs = n⌝ ∗ l ↦∗ vs ∗ [∗ listZ] k↦v ∈ vs, Q k v
      }]].
    Proof.
      iIntros (Hn Φ) "Hf HΦ". wp_lam. wp_alloc l as "Hl"; first done.
      wp_smart_apply (twp_array_init_loop _ _ _ 0 n (Z.to_nat n) with "[Hl Hf] [HΦ]").
      { by rewrite /= Z2Nat.id; last lia. }
      { rewrite loc_add_0 Z2Nat.id; last lia. iFrame. }
      iIntros (vs). iDestruct 1 as (Hlen) "[Hl Hvs]". wp_pures.
      iApply ("HΦ" $! _ vs). iModIntro. iSplit.
      { iPureIntro. lia. }
      rewrite loc_add_0. iFrame.
    Qed.
  End array_init.

  Section array_init_fmap.
    Context {A} (g : A → val) (Q : Z → A → iProp Σ).
    Implicit Types (xs : list A) (f : val).

    Local Lemma big_sepLZ_exists_eq vs :
      ([∗ listZ] k↦v ∈ vs, ∃ x, ⌜v = g x⌝ ∗ Q k x) -∗
      ∃ xs, ⌜ vs = g <$> xs ⌝ ∗ [∗ listZ] k↦x ∈ xs, Q k x.
    Proof.
      iIntros "Hvs". iInduction vs as [|v vs] "IH" forall (Q); simpl.
      { iExists []. by auto. }
      iDestruct "Hvs" as "[(%x & -> & Hv) Hvs]".
      setoid_rewrite Nat2Z.inj_succ.
      iDestruct ("IH" $! (λ k x, Q (Z.succ k) x) with "Hvs") as (xs ->) "Hxs".
      iExists (x :: xs). iSplitR; first done.
      rewrite big_sepLZ_cons. by iFrame.
    Qed.

    Lemma wp_array_init_fmap stk E n f :
      (0 < n)%Z →
      {{{
        [∗ list] (i:Z) ∈ seqZ 0 n,
          WP f #i @ stk; E {{ v, ∃ x, ⌜v = g x⌝ ∗ Q i x }}
      }}}
        array_init #n f @ stk; E
      {{{ l xs, RET #l;
        ⌜lengthZ xs = n⌝ ∗ l ↦∗ (g <$> xs) ∗ [∗ listZ] k↦x ∈ xs, Q k x
      }}}.
    Proof.
      iIntros (Hn Φ) "Hf HΦ". iApply (wp_array_init with "Hf"); first done.
      iIntros "!>" (l vs). iDestruct 1 as (<-) "[Hl Hvs]".
      iDestruct (big_sepLZ_exists_eq with "Hvs") as (xs ->) "Hxs".
      iApply "HΦ". iFrame "Hl Hxs". by rewrite fmap_lengthZ.
    Qed.
    Lemma twp_array_init_fmap stk E n f :
      (0 < n)%Z →
      [[{
        [∗ list] (i:Z) ∈ seqZ 0 n,
          WP f #i @ stk; E [{ v, ∃ x, ⌜v = g x⌝ ∗ Q i x }]
      }]]
        array_init #n f @ stk; E
      [[{ l xs, RET #l;
        ⌜lengthZ xs = n⌝ ∗ l ↦∗ (g <$> xs) ∗ [∗ listZ] k↦x ∈ xs, Q k x
      }]].
    Proof.
      iIntros (Hn Φ) "Hf HΦ". iApply (twp_array_init with "Hf"); first done.
      iIntros (l vs). iDestruct 1 as (<-) "[Hl Hvs]".
      iDestruct (big_sepLZ_exists_eq with "Hvs") as (xs ->) "Hxs".
      iApply "HΦ". iFrame "Hl Hxs". by rewrite fmap_lengthZ.
    Qed.
  End array_init_fmap.
End proof.
