From iris.heap_lang Require Export tactics derived.
Import uPred.

(** wp-specific helper tactics *)
Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etrans; [|fast_by apply (wp_bind K)]; simpl
  end.

(* Solves side-conditions generated by the wp tactics *)
Ltac wp_done :=
  match goal with
  | |- Closed _ _ => solve_closed
  | |- is_Some (to_val _) => solve_to_val
  | |- to_val _ = Some _ => solve_to_val
  | |- language.to_val _ = Some _ => solve_to_val
  | _ => fast_done
  end.

Ltac wp_value_head := etrans; [|eapply wp_value; wp_done]; lazy beta.

Ltac wp_strip_later := idtac. (* a hook to be redefined later *)

Ltac wp_seq_head :=
  lazymatch goal with
  | |- _ ⊢ wp ?E (Seq _ _) ?Q =>
    etrans; [|eapply wp_seq; wp_done]; wp_strip_later
  end.

Ltac wp_finish := intros_revert ltac:(
  rewrite /= ?to_of_val;
  try wp_strip_later;
  repeat lazymatch goal with
  | |- _ ⊢ wp ?E (Seq _ _) ?Q =>
     etrans; [|eapply wp_seq; wp_done]; wp_strip_later
  | |- _ ⊢ wp ?E _ ?Q => wp_value_head
  end).

Tactic Notation "wp_value" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    wp_bind_core K; wp_value_head) || fail "wp_value: cannot find value in" e
  | _ => fail "wp_value: not a wp"
  end.

Lemma of_val_unlock v e : of_val v = e → of_val (locked v) = e.
Proof. by unlock. Qed.

(* Applied to goals that are equalities of expressions. Will try to unlock the
   LHS once if necessary, to get rid of the lock added by the syntactic sugar. *)
Ltac solve_of_val_unlock := try apply of_val_unlock; reflexivity.

Tactic Notation "wp_rec" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with App ?e1 _ =>
(* hnf does not reduce through an of_val *)
(*      match eval hnf in e1 with Rec _ _ _ => *)
    wp_bind_core K; etrans;
      [|eapply wp_rec; [solve_of_val_unlock|wp_done..]]; simpl_subst; wp_finish
(*      end *) end) || fail "wp_rec: cannot find 'Rec' in" e
  | _ => fail "wp_rec: not a 'wp'"
  end.

Tactic Notation "wp_lam" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with App ?e1 _ =>
(*    match eval hnf in e1 with Rec BAnon _ _ => *)
    wp_bind_core K; etrans;
      [|eapply wp_lam; [solve_of_val_unlock|wp_done..]]; simpl_subst; wp_finish
(*    end *) end) || fail "wp_lam: cannot find 'Lam' in" e
  | _ => fail "wp_lam: not a 'wp'"
  end.

Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_let.

Tactic Notation "wp_op" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    lazymatch eval hnf in e' with
    | BinOp LtOp _ _ => wp_bind_core K; apply wp_lt; wp_finish
    | BinOp LeOp _ _ => wp_bind_core K; apply wp_le; wp_finish
    | BinOp EqOp _ _ =>
       wp_bind_core K; eapply wp_eq; [wp_done|wp_done|wp_finish|wp_finish]
    | BinOp _ _ _ =>
       wp_bind_core K; etrans;
         [|eapply wp_bin_op; [wp_done|wp_done|try fast_done]]; wp_finish
    | UnOp _ _ =>
       wp_bind_core K; etrans;
         [|eapply wp_un_op; [wp_done|try fast_done]]; wp_finish
    end) || fail "wp_op: cannot find 'BinOp' or 'UnOp' in" e
  | _ => fail "wp_op: not a 'wp'"
  end.

Tactic Notation "wp_proj" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | Fst _ => wp_bind_core K; etrans; [|eapply wp_fst; wp_done]; wp_finish
    | Snd _ => wp_bind_core K; etrans; [|eapply wp_snd; wp_done]; wp_finish
    end) || fail "wp_proj: cannot find 'Fst' or 'Snd' in" e
  | _ => fail "wp_proj: not a 'wp'"
  end.

Tactic Notation "wp_if" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | If _ _ _ =>
      wp_bind_core K;
      etrans; [|eapply wp_if_true || eapply wp_if_false]; wp_finish
    end) || fail "wp_if: cannot find 'If' in" e
  | _ => fail "wp_if: not a 'wp'"
  end.

Tactic Notation "wp_match" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | Case _ _ _ =>
      wp_bind_core K;
      etrans; [|first[eapply wp_match_inl; wp_done|eapply wp_match_inr; wp_done]];
      simpl_subst; wp_finish
    end) || fail "wp_match: cannot find 'Match' in" e
  | _ => fail "wp_match: not a 'wp'"
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_core K
    end) || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.
