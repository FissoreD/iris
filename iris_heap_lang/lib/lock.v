From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** A general interface for a lock.

All parameters are implicit, since it is expected that there is only one
[heapGS_gen] in scope that could possibly apply.

Only one instance of this class should ever be in scope. To write a library that
is generic over the lock, just add a [`{lock}] implicit parameter. To use a
particular lock instance, use [Local Existing Instance <lock instance>].

When writing an instance of this class, please take care not to shadow the class
projections (e.g., either use [Local Definition newlock] or avoid the name
[newlock] altogether), and do not register an instance -- just make it a
[Definition] that others can register later. *)
Class lock `{!heapGS_gen hlc Σ} := Lock {
  (** * Operations *)
  newlock : val;
  acquire : val;
  release : val;
  (** * Predicates *)
  (** [name] is used to associate locked with [is_lock] *)
  lock_name : Type;
  (** No namespace [N] parameter because we only expose program specs, which
  anyway have the full mask. *)
  is_lock (γ: lock_name) (lock: val) (R: iProp Σ) : iProp Σ;
  locked (γ: lock_name) : iProp Σ;
  (** * General properties of the predicates *)
  is_lock_persistent γ lk R :> Persistent (is_lock γ lk R);
  is_lock_iff γ lk R1 R2 :
    is_lock γ lk R1 -∗ ▷ □ (R1 ∗-∗ R2) -∗ is_lock γ lk R2;
  locked_timeless γ :> Timeless (locked γ);
  locked_exclusive γ : locked γ -∗ locked γ -∗ False;
  (** * Program specs *)
  newlock_spec (R : iProp Σ) :
    {{{ R }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R }}};
  acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} acquire lk {{{ RET #(); locked γ ∗ R }}};
  release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}
}.
Global Hint Mode lock + + + : typeclass_instances.

Global Instance is_lock_contractive `{!heapGS_gen hlc Σ, !lock} γ lk :
  Contractive (is_lock γ lk).
Proof.
  apply (uPred.contractive_internal_eq (M:=iResUR Σ)).
  iIntros (P Q) "#HPQ". iApply prop_ext. iIntros "!>".
  iSplit; iIntros "H"; iApply (is_lock_iff with "H");
    iNext; iRewrite "HPQ"; auto.
Qed.

Global Instance is_lock_proper `{!heapGS_gen hlc Σ, !lock} γ lk :
  Proper ((≡) ==> (≡)) (is_lock γ lk) := ne_proper _.
