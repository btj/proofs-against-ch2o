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
Require Export ch2o.axiomatic.axiomatic_expressions.
Require Export ch2o.axiomatic.axiomatic_statements.
Require Export ch2o.axiomatic.axiomatic_adequate.
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

Lemma mem_lock_cmap (Γ: env K) o (m: indexmap (cmap_elem K (pbit K))):
  mem_lock Γ (addr_top o sintT%BT) (CMap m) =
  CMap (alter (cmap_elem_map (ctree_map pbit_lock)) o m).
reflexivity.
Qed.

Lemma zip_with_pbit_unlock_if_list_fmap_pbit_lock (l: list (pbit K)):
  Forall (λ γb, Some Writable ⊆ pbit_kind γb) l ->
  zip_with pbit_unlock_if (pbit_lock <$> l) (replicate (Datatypes.length l) true) = l.
induction l; intros; try reflexivity.
simpl.
unfold fmap in IHl.
rewrite IHl.
- destruct a.
  simpl.
  inversion H; subst.
  destruct tagged_perm.
  + destruct l0; simpl in *.
    * unfold perm_kind in H2.
      elim H2.
    * reflexivity.
  + elim H2.
- inversion H; subst; assumption.
Qed.

Lemma mem_unlock_lock_singleton (Γ: env K) o (m: mem K):
  ✓{Γ} m ->
  '{m} !! o = Some (sintT%T, false) ->
  mem_writable Γ (addr_top o sintT%BT) m ->
  mem_unlock
    (lock_singleton Γ (addr_top o sintT%BT))
    (mem_lock Γ (addr_top o sintT%BT) m) = m.
destruct m as [m].
intros Hvalid. intros.
destruct Hvalid as [Hvalid1 [Hvalid2 Hvalid3]].
simpl in *.
assert (forall (m1: indexmap (cmap_elem K (pbit K))) m2, m1 = m2 -> CMap m1 = CMap m2). { intros; congruence. }
apply H1.
apply map_eq.
intro i.
rewrite lookup_merge.
2:reflexivity.
destruct (decide (i = o)).
- subst.
  rewrite lookup_singleton.
  rewrite lookup_alter.
  destruct H0 as [w [Hw H'w]].
  simpl in *.
  unfold cmap_lookup in Hw.
  simpl in Hw.
  case_eq (m !! o); intros; rewrite H0 in Hw; try discriminate.
  destruct c; try discriminate.
  simpl in Hw.
  injection Hw; clear Hw; intros; subst.
  simpl.
  rewrite lookup_fmap in H.
  rewrite H0 in H.
  simpl in H.
  injection H; clear H; intros; subst.
  destruct w; try discriminate.
  destruct b0; try discriminate.
  destruct i; try discriminate.
  simpl in H.
  injection H; clear H; intros; subst.
  clear H1.
  simpl.
  pose proof H0.
  apply Hvalid3 in H0.
  destruct H0 as [τ [Ho1 [Ho2 [Ho3 Ho4]]]].
  simpl in *.
  unfold typed in Ho1.
  unfold index_typed in Ho1.
  destruct Ho1 as [β Ho1].
  rewrite lookup_fmap in Ho1.
  rewrite H in Ho1.
  simpl in Ho1.
  injection Ho1; clear Ho1; intros; subst.
  simpl in Ho3.
  unfold typed in Ho3.
  unfold ctree_typed in Ho3.
  simpl in Ho3.
  inversion Ho3; subst.
  rewrite fmap_length.
  assert (Datatypes.length l = 32). {
    rewrite H4.
    reflexivity.
  }
  rewrite H0.
  assert (natmap.to_bools 32
              {|
              mapset.mapset_car := natmap.list_to_natmap
                                     [Some (); Some (); Some (); 
                                     Some (); Some (); Some (); 
                                     Some (); Some (); Some (); 
                                     Some (); Some (); Some (); 
                                     Some (); Some (); Some (); 
                                     Some (); Some (); Some (); 
                                     Some (); Some (); Some (); 
                                     Some (); Some (); Some (); 
                                     Some (); Some (); Some (); 
                                     Some (); Some (); Some (); 
                                     Some (); Some ()] |} =
    [true; true; true; true; true; true; true; true;
     true; true; true; true; true; true; true; true;
     true; true; true; true; true; true; true; true;
     true; true; true; true; true; true; true; true]).
  reflexivity.
  rewrite H1.
  pose proof (zip_with_pbit_unlock_if_list_fmap_pbit_lock l H'w).
  rewrite H0 in H5.
  simpl in H5.
  rewrite H5.
  reflexivity.
- rewrite lookup_singleton_ne; try congruence.
  rewrite lookup_alter_ne; try congruence.
Qed.

Lemma lockset_union_right_id (Ω: lockset): Ω ∪ ∅ = Ω.
apply lockset_eq.
intros.
solve_elem_of.
Qed.

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

Lemma expr_eval_call_None {Γ: env K} {ρ m} {E: ectx K} {f args ν}:
  ⟦ subst E (ECall f args) ⟧ Γ ρ m = Some ν -> False.
intros.
apply expr_eval_subst in H.
destruct H.
destruct H.
simpl in H.
discriminate.
Qed.

Lemma expr_eval_no_locks (Γ: env K) ρ m Ω ν ν':
  ⟦ %#{Ω} ν ⟧ Γ ρ m = Some ν' -> (%#{Ω} ν = %# ν')%E.
intros.
simpl in H.
unfold mguard in H.
unfold option_guard in H.
destruct (lockset_eq_dec Ω ∅); congruence.
Qed.

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

Definition safe S0: Prop := forall S, rtc (cstep Γ δ) S0 S -> ~ is_undef_state S.

Lemma call_safe_lemma: forall f s,
  δ !! f = Some s ->
  safe (State [] (Stmt ↘ s) ∅) ->
  safe (State [] (Call f []) ∅).
Admitted.

Require Export ch2o.axiomatic.axiomatic_simple.

Lemma call_main_safe: safe (State [] (Call "main" []) ∅).
eapply call_safe_lemma. reflexivity.
assert ((intT (to_inttype
                        {|
                        csign := None;
                        crank := CIntRank |}))%BT = (sintT%BT : base_type K)). reflexivity.
rewrite H; clear H.
assert (IntType (from_option Signed (Some Signed)) int_rank = (sintT%IT: int_type K)). reflexivity.
rewrite H; clear H.
intros S HS1 HS2.
destruct ax_stmt_adequate with (7:=HS1) (Q:=fun (v: val K) => True%A) (cmτ:=((true, Some sintT%T): rettype K)) as [[n' [m' [Had1 Had2]]] | [[n' [m' [v [Had1 Had2]]]] | Had3]].
Focus 7. {
  subst. elim (is_Some_None HS2).
} Unfocus.
Focus 7. {
  subst. elim (is_Some_None HS2).
} Unfocus.
Focus 7. {
  inversion Had3.
  destruct S as [k [] m]; try elim (is_Some_None HS2).
  inversion H.
} Unfocus.
{ apply Γ_valid. }
{ apply δ_valid. }
{ apply m0_valid. }
{ apply mem_locks_empty. }
{ apply type_check_sound.
  - simpl. apply Γ_valid.
  - reflexivity.
}
clear S HS1 HS2.
apply ax_local.
assert ((assert_eq_mem (cmap_erase ∅)↑)%A ⊆{Γ,δ} (emp%A: assert K)). {
  rewrite cmap_erase_empty.
  unfold subseteqE.
  unfold assert_entails.
  intros.
  unfold assert_eq_mem in H5.
  unfold assert_Prop.
  simpl in *.
  tauto.
}
eapply ax_stmt_weaken_pre. {
  rewrite H.
  rewrite (right_id _ (★)%A).
  reflexivity.
}
assert (Inhabited (ptr K)). {
  constructor.
  apply NULL.
  constructor.
  apply (sintT%T).
}
eapply ax_comp.
- eapply ax_do' with
     (Q:=(var 0 ↦{false,perm_lock perm_full} (# intV{sintT} 3) : sintT%BT)%A)
     (Q':=(var 0 ↦{false,perm_full} (# intV{sintT} 3) : sintT%BT)%A).
  + eapply ax_expr_weaken_pre. {
      rewrite assert_singleton_l_.
      reflexivity.
    }
    apply ax_expr_exist_pre.
    intro x.
    eapply ax_expr_weaken_post'. {
      apply assert_singleton_l_2 with (a:=x).
    }
    eapply ax_expr_invariant_l'.
    eapply ax_assign_r' with (p:=x).
    * apply ax_var'.
      rewrite (right_id _ (★)%A).
      rewrite (right_id _ (★)%A).
      apply assert_and_l.
    * eapply ax_cast'.
      -- eapply ax_expr_base.
         eapply assert_and_intro.
         Focus 2. {
           apply assert_int_typed_eval.
           constructor; (unfold int_lower || unfold int_upper); simpl; lia.
         } Unfocus.
         simpl.
         rewrite assert_Prop_l.
         ++ reflexivity.
         ++ reflexivity.
      -- apply assert_eval_int_cast_self'.
         apply assert_int_typed_eval.
         constructor; (unfold int_lower || unfold int_upper); simpl; lia.
    * simpl.
      apply assert_and_intro.
      -- apply assert_eval_int_cast_self'.
         apply assert_int_typed_eval.
         constructor; (unfold int_lower || unfold int_upper); simpl; lia.
      -- apply assert_eval_int_cast_self'.
         apply assert_int_typed_eval.
         constructor; (unfold int_lower || unfold int_upper); simpl; lia.
    * simpl (freeze true _).
      rewrite <- (right_id _ (★)%A) at 1.
      apply assert_sep_preserving.
      -- reflexivity.
      -- apply assert_wand_intro.
         rewrite (left_id _ (★)%A).
         reflexivity.
    * reflexivity.
  + apply assert_lock_singleton.
    * apply perm_full_valid.
    * reflexivity.
- apply ax_ret with (Q1:=(fun _ => var 0 ↦{false, perm_full} # intV{sintT} 3 : sintT%BT)%A).
  + intros.
    rewrite <- assert_unlock_sep.
    rewrite stack_indep.
    rewrite <- unlock_indep.
    rewrite <- (right_id _ (★)%A) at 1.
    apply assert_sep_preserving. 2:apply assert_True_intro.
    rewrite assert_unlock_exists.
    apply assert_exist_intro with (x:=intV{sintT} 3).
    apply assert_singleton_unlock_indep.
    reflexivity.
  + eapply ax_expr_base.
    apply assert_and_intro.
    * reflexivity.
    * rewrite <- assert_eval_int_cast.
      -- apply assert_singleton_eval.
         reflexivity.
      -- constructor; (unfold int_lower || unfold int_upper); simpl; lia.
Qed.

Goal forall S, rtc (cstep Γ δ) S0 S -> ~ is_undef_state S.
intros.
apply call_main_safe with (1:=H).
Qed.
