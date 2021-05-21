Require Export ch2o.prelude.orders.
Require Export ch2o.abstract_c.architectures.
Require Export ch2o.abstract_c.interpreter.
Require Export ch2o.core_c.smallstep.
Require Export ch2o.core_c.restricted_smallstep.
Require Export ch2o.core_c.expression_eval_smallstep.
Require Export one_local.

Definition get_right{A B}(v: A + B)(H: match v with inl _ => False | inr _ => True end): B.
destruct v.
elim H.
exact b.
Defined.

Open Local Scope string_scope.

Definition A: architecture := {|
  arch_sizes := architectures.lp64;
  arch_big_endian := false;
  arch_char_signedness := Signed;
  arch_alloc_can_fail := false
|}.
Notation K := (arch_rank A).

Notation M := (error (frontend_state K) string).

Definition to_core_c_program: M (env K * funenv K * state K) :=
  _ ← alloc_program decls;
  Δg ← gets to_globals;
  '(_,σs,σ,_) ← error_of_option (Δg !! "main"≫= maybe4 Fun)
    ("function `main` undeclared`");
  guard (σ = sintT%T ∨ σ = uintT%T) with
    ("function `main` should have return type `int`");
  Γ ← gets to_env;
  δ ← gets to_funenv;
  m ← gets to_mem;
  mret (Γ, δ, initial_state m "main" []).

Definition to_core_c_program_result: string + env K * funenv K * state K :=
  error_eval to_core_c_program ∅.

Lemma to_core_c_program_ok: match to_core_c_program_result with inl _ => False | inr _ => True end.
exact I.
Qed.

Definition core_c_program: env K * funenv K * state K := get_right to_core_c_program_result to_core_c_program_ok.

Definition Γ: env K := fst (fst core_c_program).
Definition δ: funenv K := snd (fst core_c_program).
Definition S0 := snd core_c_program.

Lemma call_main_safe: forall S, rtc (cstep Γ δ) (State [] (Call "main" []) ∅) S -> ~ is_undef_state S.
intros.
apply csteps_rcsteps in H.
inv_rcsteps H. {
  inversion 1.
  simpl in H.
  elim (is_Some_None H).
}
inversion H; clear H; subst.
assert (match Some s with None => s | Some s => s end = s). {
  reflexivity.
}
rewrite <- H6 in H.
simpl in H.
subst.
clear H6.
destruct os; simpl in H8; try discriminate; clear H8.
clear H7.
inversion H1; subst; clear H1. {
  inversion 1.
  simpl in H.
  elim (is_Some_None H).
}
simpl in H.
Opaque mem_alloc.
inv_rcstep.
clear H y.
inv_rcsteps H0. {
  inversion 1.
  elim (is_Some_None H).
}
inv_rcstep.
clear y.
inv_rcsteps H1. {
  inversion 1.
  elim (is_Some_None H).
}
inv_rcstep.
clear y.
Lemma assign_pure (Γ: env K) δ ρ S0 S:
  Γ\ δ\ ρ ⊢ₛ S0 ⇒* S ->
  is_undef_state S ->
  forall k el er m νl νr,
  S0 = State k (Expr (el ::= er)) m ->
  ⟦ el ⟧ Γ (rlocals ρ k) m = Some νl ->
  ⟦ er ⟧ Γ (rlocals ρ k) m = Some νr ->
  Γ\ δ\ ρ ⊢ₛ State k (Expr (%# νl ::= %# νr)) m ⇒* S.
induction 1; intros; subst. {
  elim (is_Some_None H).
}
inversion H; clear H; subst.
- (* head reduction *)
Lemma cons_snoc0 {A} x (xs: list A): exists y ys, x::xs = (ys ++ [y])%list.
revert x.
induction xs.
- intros.
  exists x.
  exists [].
  reflexivity.
- intros.
  destruct (IHxs a) as [y [ys Hyys]].
  rewrite Hyys.
  exists y.
  exists (x::ys).
  reflexivity.
Qed.
  destruct E.
  + (* empty evaluation context *)
    simpl in *.
    subst.
    inversion H8; subst.
    simpl in *.
    unfold mguard in H4.
    unfold option_guard in H4.
    case_eq (lockset_eq_dec Ω2 ∅); intros.
    * rewrite H in H4.
      injection H4; clear H4; intros; subst.
      unfold mguard in H3; unfold option_guard in H3.
      case_eq (lockset_eq_dec Ω1 ∅); intros.
      -- rewrite H2 in H3.
         injection H3; clear H3; intros; subst.
         clear H H2.
         eapply rtc_l.
         ++ eapply rcstep_expr_head with (E:=[]).
            eassumption.
         ++ eassumption.
      -- rewrite H2 in H3; discriminate.
    * rewrite H in H4; discriminate.
  + (* nonempty evaluation context *)
    destruct (cons_snoc0 e E) as [e' [E' H']].
    rewrite H' in *.
    clear H' e E.
    rewrite subst_snoc in H6.
    destruct e'; try discriminate.
    * (* lhs *)
      simpl in H6.
      injection H6; clear H6; intros; subst.
      rewrite subst_snoc in H0.
      rewrite subst_snoc in IHrtc.
      simpl in *.
Lemma expr_eval_pure (Γ: env K) ρ e1 m e2 m2 (E: ectx K) ν:
  Γ\ ρ ⊢ₕ e1, m ⇒ e2, m2 ->
  ⟦ subst E e1 ⟧ Γ ρ m = Some ν ->
  m2 = m.
intros.
apply expr_eval_subst in H0.
destruct H0 as [ν' [Hν' _]].
apply symmetry.
apply ehstep_expr_eval_mem with (1:=H) (2:=Hν').
Qed.
Lemma expr_eval_complete_subst (Γ: env K) ρ e1 m e2 m2 (E: ectx K) ν:
  Γ\ ρ ⊢ₕ e1, m ⇒ e2, m2 ->
  ⟦ subst E e1 ⟧ Γ ρ m = Some ν ->
  ⟦ subst E e2 ⟧ Γ ρ m = Some ν.
intros.
pose proof H0.
apply expr_eval_subst in H0.
destruct H0 as [ν' [Hν' _]].
assert (m = m2). {
  apply ehstep_expr_eval_mem with (1:=H) (2:=Hν').
}
subst m2.
assert (⟦ e2 ⟧ Γ ρ m = Some ν'). {
  apply ehstep_expr_eval with (1:=H) (2:=Hν') (3:=Hν').
}
rewrite subst_preserves_expr_eval with (e4:=e2) in H1.
- assumption.
- congruence.
Qed.
      assert (m2 = m). {
        apply expr_eval_pure with (1:=H8) (2:=H3).
      }
      subst m2.
      apply expr_eval_complete_subst with (1:=H8) in H3.
      apply IHrtc with (3:=H3) (4:=H4); trivial.
    * (* rhs *)
      simpl in *.
      injection H6; clear H6; intros; subst.
      rewrite subst_snoc in H0.
      rewrite subst_snoc in IHrtc.
      simpl in *.
      assert (m2 = m). {
        apply expr_eval_pure with (1:=H8) (2:=H4).
      }
      subst m2.
      apply expr_eval_complete_subst with (1:=H8) in H4.
      apply IHrtc with (3:=H3) (4:=H4); trivial.
- (* function call *)
  destruct E.
  + (* E = [] *)
    simpl in *.
    discriminate.
  + destruct (cons_snoc0 e0 E) as [e' [E' H']].
    rewrite H' in *.
    clear H' e0 E.
    rewrite subst_snoc in H6.
    destruct e'; try discriminate; simpl in *; injection H6; clear H6; intros; subst.
    * (* lhs *)
Lemma expr_eval_call_None {Γ: env K} {ρ m} {E: ectx K} {f args ν}:
  ⟦ subst E (ECall f args) ⟧ Γ ρ m = Some ν -> False.
intros.
apply expr_eval_subst in H.
destruct H.
destruct H.
simpl in H.
discriminate.
Qed.
      elim (expr_eval_call_None H3).
    * (* rhs *)
      elim (expr_eval_call_None H4).
- (* undef *)
  destruct E.
  * (* E = [] *)
    simpl in *.
    subst.
    eapply rtc_l.
    2: eassumption.
    inversion H8; subst.
    destruct H5.
    destruct H7.
Lemma expr_eval_no_locks (Γ: env K) ρ m Ω ν ν':
  ⟦ %#{Ω} ν ⟧ Γ ρ m = Some ν' -> (%#{Ω} ν = %# ν')%E.
intros.
simpl in H.
unfold mguard in H.
unfold option_guard in H.
destruct (lockset_eq_dec Ω ∅); congruence.
Qed.
    rewrite expr_eval_no_locks with (1:=H3) in *.
    rewrite expr_eval_no_locks with (1:=H4) in *.
    apply rcstep_expr_undef with (E:=[]).
    -- assumption.
    -- assumption.
  * (* E <> [] *)
    destruct (cons_snoc0 e0 E) as [e' [E' H']].
    rewrite H' in *.
    clear H' e0 E.
    rewrite subst_snoc in H5.
    destruct e'; try discriminate; simpl in *; injection H5; clear H5; intros; subst.
    -- (* lhs *)
       destruct expr_eval_subst_ehstep with (1:=H3) (2:=H8).
       destruct H.
       elim H9.
       eapply ehsafe_step.
       apply H.
    -- (* rhs *)
       destruct expr_eval_subst_ehstep with (1:=H4) (2:=H8).
       destruct H.
       elim H9.
       eapply ehsafe_step.
       apply H.
Qed.
Lemma assign_pure' (Γ: env K) δ ρ S k el er m νl νr:
  Γ\ δ\ ρ ⊢ₛ (State k (Expr (el ::= er)) m) ⇒* S ->
  ⟦ el ⟧ Γ (rlocals ρ k) m = Some νl ->
  ⟦ er ⟧ Γ (rlocals ρ k) m = Some νr ->
  (Γ\ δ\ ρ ⊢ₛ State k (Expr (%# νl ::= %# νr)) m ⇒* S ->
   ¬ is_undef_state S) ->
  ¬ is_undef_state S.
intros.
intro.
apply H2 with (2:=H3).
apply assign_pure with (1:=H) (2:=H3) (4:=H0) (5:=H1).
reflexivity.
Qed.
eapply assign_pure' with (1:=H1); clear H1. {
  simpl.
  reflexivity.
} {
  simpl.
  rewrite option_guard_True.
  2: reflexivity.
  simpl.
  reflexivity.
}
intros.
inversion H; clear H; subst. {
  inversion 1.
  elim (is_Some_None H).
}
inv_rcstep; clear y.
- inv_ehstep.
  inversion H10; clear H10; subst.
  unfold val_cast in *.
  simpl in *.
  unfold int_cast in *.
  simpl in *.
  unfold int_pre_cast in *.
  simpl in *.
  clear H H9.
  inv_rcsteps H1. {
    inversion 1.
    elim (is_Some_None H).
  }
  inv_rcstep.
  clear y.
  inv_rcsteps H1. {
    inversion 1.
    elim (is_Some_None H).
  }
  inv_rcstep.
  clear y.
  inv_rcsteps H1. {
    inversion 1.
    elim (is_Some_None H).
  }
  inv_rcstep.
  clear y.
Lemma Expr_pure (Γ: env K) δ ρ S0 S:
  Γ\ δ\ ρ ⊢ₛ S0 ⇒* S ->
  is_undef_state S ->
  forall k e m ν,
  S0 = State k (Expr e) m ->
  ⟦ e ⟧ Γ (rlocals ρ k) m = Some ν ->
  Γ\ δ\ ρ ⊢ₛ State k (Expr (%# ν)) m ⇒* S.
intro Hrtc.
pose proof Hrtc.
induction H; intros; subst. {
  elim (is_Some_None H).
}
assert (forall Ω ν', e = (%#{Ω} ν')%E -> Γ\ δ\ ρ ⊢ₛ State k (Expr (%# ν)) m ⇒* z). {
  intros.
  subst.
  simpl in H3.
  unfold mguard in H3.
  unfold option_guard in H3.
  destruct (lockset_eq_dec Ω ∅).
  2: discriminate.
  injection H3; clear H3; intros; subst.
  assumption.
}
clear Hrtc.
inversion H; clear H; subst; try (eapply H2; reflexivity); clear H2.
- (* head reduction *)
  assert (m2 = m). {
    apply expr_eval_pure with (1:=H8) (2:=H3).
  }
  subst m2.
  eapply IHrtc; try trivial.
  apply expr_eval_complete_subst with (1:=H8) (2:=H3).
- (* function call *)
  elim (expr_eval_call_None H3).
- elim H9.
  eapply expr_eval_subst_ehsafe; eassumption.
Qed.
Lemma Expr_pure' (Γ: env K) δ ρ S k e m ν:
  Γ\ δ\ ρ ⊢ₛ (State k (Expr e) m) ⇒* S ->
  ⟦ e ⟧ Γ (rlocals ρ k) m = Some ν ->
  (Γ\ δ\ ρ ⊢ₛ State k (Expr (%# ν)) m ⇒* S ->
   ¬ is_undef_state S) ->
  ¬ is_undef_state S.
intros.
intro.
apply H1.
2: assumption.
apply Expr_pure with (1:=H) (2:=H2) (4:=H0).
reflexivity.
Qed.
  eapply Expr_pure' with (1:=H1).
  + rewrite right_id_L.
    rewrite right_id_L.
    rewrite right_id_L.
    simpl.
    rewrite option_guard_True.
    simpl.
    rewrite option_guard_True.
    simpl.
  inv_rcsteps H1. {
    inversion 1.
    elim (is_Some_None H).
  }

  

Goal forall S, rtc (cstep Γ δ) S0 S -> ~ is_undef_state S.
intros.
apply call_main_safe with (1:=H).
Qed.
