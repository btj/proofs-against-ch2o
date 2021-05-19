Require Export ch2o.abstract_c.architectures.
Require Export ch2o.abstract_c.interpreter.
Require Export ch2o.core_c.smallstep.
Require Export ch2o.core_c.restricted_smallstep.
Require Export return42.

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
inversion H; subst; clear H.
destruct E; try discriminate.
simpl in H3.
injection H3; clear H3; intros; subst.
inversion H0; clear H0; subst. {
  inversion 1.
  simpl in H.
  elim (is_Some_None H).
}
inv_rcstep.
- inversion H0; clear H0; subst.
  clear H7.
  inversion H1; clear H1; subst. {
    inversion 1.
    elim (is_Some_None H).
  }
  simpl in H.
  unfold int_cast in H.
  simpl in H.
  unfold int_pre_cast in H.
  simpl in H.
  revert H0.
  apply (rcstep_expr_inv _ _ _ (fun y => Γ\ δ\ [] ⊢ₛ y ⇒* S → ¬ is_undef_state S) _ _ _ _ _ _ H).
  clear H.
  intro H.
  rewrite mem_unlock_empty in H.
  inversion H; clear H; subst. {
    inversion 1.
    elim (is_Some_None H).
  }
  inversion H0; clear H0; subst.
  simpl in H1.
  inversion H1; clear H1; subst. {
    inversion 1.
    elim (is_Some_None H).
  }
  inversion H.
- elim H1.
  clear H0 H1 H2 S y.
  eapply ehsafe_step.
  constructor.
  constructor.
  + cbv. intro. discriminate.
  + cbv. reflexivity.
Qed.

Goal forall S, rtc (cstep Γ δ) S0 S -> ~ is_undef_state S.
intros.
apply call_main_safe with (1:=H).
Qed.
