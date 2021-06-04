Require Export Nat.
Require Export ch2o.prelude.orders.
Require Export ch2o.prelude.nmap.
Require Export ch2o.prelude.stringmap.
Require Export ch2o.memory.memory_basics.
Require Export ch2o.abstract_c.architectures.
Require Export ch2o.abstract_c.interpreter.
Require Export ch2o.abstract_c.frontend_sound.
Require Export ch2o.core_c.smallstep.
Require Export ch2o.core_c.restricted_smallstep.
Require Export ch2o.core_c.expression_eval_smallstep.
Require Export bigstep_soundness.
Require Export three_locals.

Definition get_right{A B}(v: A + B)(H: match v with inl _ => False | inr _ => True end): B.
destruct v.
elim H.
exact b.
Defined.

Local Open Scope string_scope.

Definition A: architecture := {|
  arch_sizes := architectures.lp64;
  arch_big_endian := false;
  arch_char_signedness := Signed;
  arch_alloc_can_fail := false
|}.
Notation K := (arch_rank A).

Notation M := (error (frontend_state K) string).

Lemma alloc_program_ok: match alloc_program (K:=K) decls empty with inl _ => False | inr _ => True end.
exact I.
Qed.

Definition alloc_program_result: frontend_state K.
eapply snd.
eapply get_right.
apply alloc_program_ok.
Defined.

Compute (stringmap_to_list (env_t (to_env alloc_program_result))).
Compute (stringmap_to_list (env_f (to_env alloc_program_result))).

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

Definition Γ: env K := to_env alloc_program_result.
Definition δ: funenv K := to_funenv alloc_program_result.
Definition m0: mem K := to_mem alloc_program_result.
Definition S0 := initial_state m0 "main" [].

Lemma alloc_program_eq: alloc_program decls empty = mret () alloc_program_result.
reflexivity.
Qed.

Lemma Γ_valid: ✓ Γ.
apply alloc_program_valid with (1:=alloc_program_eq).
Qed.

Lemma δ_valid: ✓{Γ,'{m0}} δ.
apply alloc_program_valid with (1:=alloc_program_eq).
Qed.

Lemma m0_valid: ✓{Γ} m0.
apply alloc_program_valid with (1:=alloc_program_eq).
Qed.

Goal forall S, rtc (cstep Γ δ) S0 S -> ~ is_undef_state S.
intros.
intro HS.
apply csteps_rcsteps in H.
inv_rcsteps H. elim (is_Some_None HS).
inversion H; clear H; subst.
destruct os; try discriminate.
clear H7 H8.
assert (match Some s with None => s | Some s => s end = s). {
  reflexivity.
}
rewrite <- H6 in H.
simpl in H.
subst.
clear H6.
assert (m0 = ∅). reflexivity.
rewrite H in H1. clear H.
simpl in H1.
apply exec_sound with (z:=2) in H1. {
  destruct H1 as [H1|[m H1]].
  - destruct S as [? [] ?]; try elim (is_Some_None HS).
    inversion H1.
    inversion H.
  - subst.
    elim (is_Some_None HS).
}
apply Γ_valid.
apply δ_valid.
{
  apply type_check_sound.
  - simpl. apply Γ_valid.
  - reflexivity.
}
clear HS H1 S.

econstructor.
econstructor.
- econstructor.
  + simpl; lia.
  + econstructor. split; (unfold int_lower || unfold int_upper); simpl; lia.
- econstructor.
  econstructor.
  + econstructor.
    * simpl; lia.
    * econstructor. split; (unfold int_lower || unfold int_upper); simpl; lia.
  + econstructor.
    econstructor.
    * econstructor.
      -- simpl; lia.
      -- econstructor.
         reflexivity.
    * econstructor.
      -- econstructor.
         reflexivity.
Qed.
