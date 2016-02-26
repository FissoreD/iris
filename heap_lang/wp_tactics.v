From algebra Require Export upred_tactics.
From heap_lang Require Export tactics derived substitution.
Import uPred.

(** wp-specific helper tactics *)
Ltac wp_bind K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etrans; [|solve [ apply (wp_bind K) ]]; simpl
  end.
Ltac wp_finish :=
  let rec go :=
  match goal with
  | |- _ ⊑ ▷ _ => etrans; [|apply later_mono; go; reflexivity]
  | |- _ ⊑ wp _ _ _ =>
    etrans; [|eapply wp_value_pvs; reflexivity];
    (* sometimes, we will have to do a final view shift, so only apply
    pvs_intro if we obtain a consecutive wp *)
    try (eapply pvs_intro;
         match goal with |- _ ⊑ wp _ _ _ => simpl | _ => fail end)
  | _ => idtac
  end in simpl; intros_revert go.

Tactic Notation "wp_rec" ">" :=
  löb ltac:(
    (* Find the redex and apply wp_rec *)
    idtac; (* <https://coq.inria.fr/bugs/show_bug.cgi?id=4584> *)
    lazymatch goal with
    | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
      match eval cbv in e' with
      | App (Rec _ _ _) _ =>
         wp_bind K; etrans;
           [|first [eapply wp_rec' | eapply wp_rec];
               repeat (reflexivity || rewrite /= to_of_val)];
           simpl_subst; wp_finish
      end)
     end).
Tactic Notation "wp_rec" := wp_rec>; try strip_later.

Tactic Notation "wp_lam" ">" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | App (Rec "" _ _) _ =>
       wp_bind K; etrans;
         [|eapply wp_lam; repeat (reflexivity || rewrite /= to_of_val)];
         simpl_subst; wp_finish
    end)
  end.
Tactic Notation "wp_lam" := wp_lam>; try strip_later.

Tactic Notation "wp_let" ">" := wp_lam>.
Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" ">" := wp_let>.
Tactic Notation "wp_seq" := wp_let.

Tactic Notation "wp_op" ">" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | BinOp LtOp _ _ => wp_bind K; apply wp_lt; wp_finish
    | BinOp LeOp _ _ => wp_bind K; apply wp_le; wp_finish
    | BinOp EqOp _ _ => wp_bind K; apply wp_eq; wp_finish
    | BinOp _ _ _ =>
       wp_bind K; etrans; [|eapply wp_bin_op; reflexivity]; wp_finish
    | UnOp _ _ =>
       wp_bind K; etrans; [|eapply wp_un_op; reflexivity]; wp_finish
    end)
  end.
Tactic Notation "wp_op" := wp_op>; try strip_later.

Tactic Notation "wp_if" ">" :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval cbv in e' with
    | If _ _ _ =>
       wp_bind K;
       etrans; [|apply wp_if_true || apply wp_if_false]; wp_finish
    end)
  end.
Tactic Notation "wp_if" := wp_if>; try strip_later.

Tactic Notation "wp_focus" open_constr(efoc) :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match e' with efoc => unify e' efoc; wp_bind K end)
  end.

Tactic Notation "wp" ">" tactic(tac) :=
  match goal with
  | |- _ ⊑ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' => wp_bind K; tac)
  end.
Tactic Notation "wp" tactic(tac) := (wp> tac); [try strip_later|..].

(* In case the precondition does not match.
   TODO: Have one tactic unifying wp and ewp. *)
Tactic Notation "ewp" tactic(tac) := wp (etrans; [|tac]).
Tactic Notation "ewp" ">" tactic(tac) := wp> (etrans; [|tac]).
