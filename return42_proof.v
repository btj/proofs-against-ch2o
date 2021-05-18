Require Export ch2o.abstract_c.architectures.
Require Export ch2o.abstract_c.interpreter.
Require Export ch2o.core_c.smallstep.
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

Check δ.

Check (stringmap.stringmap_lookup "main" δ).

Check (δ !! "main").

Lemma call_main_safe: forall S, rtc (cstep Γ δ) (State [] (Call "main" []) ∅) S -> ~ is_undef_state S.
intros.
inversion H.
- inversion 1.
  simpl in H2.
  elim (is_Some_None H2).
- subst.
  inversion H0.
  cbv beta iota zeta delta - [lockset_empty] in H7.
  Notation int := (IntType Signed {|arch_rank_car := IntRank|}).
  assert (forall {X} (x y: X), Some x = Some y -> x = y). {
  injection 1; tauto.
  }
  apply H10 in H7.
  subst.
  inversion H1.
  + inversion 1.
    simpl in H5.
    discriminate.
  + subst.
    inversion H2.
    subst.
    destruct E; try discriminate.
    simpl in H6.
    injection H6; clear H6; intros; subst.
    inversion H3.
    * inversion 1.
      simpl in H7.
      discriminate.
    * subst.
      inversion H4.
      ++ subst.
         destruct E; try discriminate.
         -- simpl in H11.
            subst.
            inversion H13.
            subst.
            destruct os; simpl in H9; try discriminate.
            clear H8 H9 H10 H0 H1 H2 H3 H4 H13.
            clear H H16.
            simpl in H5.
            inversion H5.
            subst.
            ** inversion 1.
               simpl in H.
               elim (is_Some_None H).
            ** subst.
               (* Hier wordt Coq ondraaglijk traag... *)
               inversion H; subst.


Goal forall S, rtc (cstep Γ δ) S0 S -> ~ is_undef_state S.
intros.
intro.
inversion H.
- subst.
  simpl in H0.
  inversion H0.
  discriminate.
- unfold 
  
