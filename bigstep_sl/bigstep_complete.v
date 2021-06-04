Require Export bigstep.
Require Export ch2o.core_c.expressions.
Require Export ch2o.core_c.statements.
Require Export ch2o.core_c.smallstep.
Require Export ch2o.core_c.restricted_smallstep.
Require Export ch2o.axiomatic.assertions.
Require Export stack_assertions.

Inductive simple_expr `{Env K}: expr K -> Prop :=
| simple_expr_val_int z:
  simple_expr (# intV{sintT} z)
| simple_expr_load_var i:
  simple_expr (load (var i))
.

Inductive simple_stmt `{Env K}: stmt K -> Prop :=
| simple_stmt_local s:
  simple_stmt s ->
  simple_stmt (local{sintT%T} s)%S
| simple_stmt_ret e:
  simple_expr e ->
  simple_stmt (ret e)
| simple_stmt_assign i e:
  simple_expr e ->
  simple_stmt (var i ::= e)
| simple_stmt_seq s1 s2:
  simple_stmt s1 ->
  simple_stmt s2 ->
  simple_stmt (s1 ;; s2)
.

Section Program.

Context `{EnvSpec K} (Γ: env K) (δ: funenv K).

Lemma eval_complete st e z ρ m:
  simple_expr e →
  (Γ,'{m},(λ _, sintT%T) <$> st) ⊢ e : inr sintT%T →
  assert_holds (assert_stack st) Γ '{m} δ ρ 0 m →
   ⟦ e ⟧ Γ ρ m = Some (inr (intV{sintT} z)) →
  eval st e z.
Proof.
intro He; revert st z ρ m; induction He; intros.
- (* simple_expr_val_int *)
  simpl in H3.
  rewrite option_guard_True in H3; [|reflexivity].
  injection H3; clear H3; intros; subst.
  constructor.
  inversion H1. inversion H7. subst. inversion H10. subst. inversion H6. assumption.
- simpl in H3.
  case_eq (ρ !! i); intros.
  + rewrite H4 in H3.
    destruct p as [o τ].
    simpl in H3.
Admitted.

Lemma exec_complete st s O ρ m:
  simple_stmt s ->
  assert_holds (assert_stack st) Γ '{m} δ ρ 0 m →
  (∀ S,
   Γ\ δ\ ρ ⊢ₛ State [] (Stmt ↘ s) m ⇒* S →
   red (rcstep Γ δ ρ) S ∨
   ∃ m',
   match O with
     onormal st' =>
     assert_holds (assert_stack st') Γ '{m'} δ ρ 0 m' ∧
     S = State [] (Stmt ↗ s) m'
   | oreturn z =>
     S = State [] (Stmt (⇈ (intV{sintT} z)) s) m'
   end) →
  exec st s O.
Proof.
Admitted.

Theorem bigstep_complete s z:
  simple_stmt s ->
  (∀ S,
   Γ\ δ ⊢ₛ State [] (Stmt ↘ s) ∅ ⇒* S →
   red (cstep Γ δ) S ∨
   ∃ m', S = State [] (Stmt (⇈ (intV{sintT} z)) s) m') →
  exec [] s (oreturn z).
Proof.
Admitted.