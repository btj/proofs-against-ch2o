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
set (m1:=mem_alloc Γ o false perm_full (val_new Γ sintT%BT) ∅).
assert (H: Γ\ δ\ [] ⊢ₛ State [CLocal o sintT%BT; CParams "main" []]
                   (Stmt ↘
                      (var 0 ::= cast{sintT%BT} (# intV{sintT} 3) ;;
                       ret (cast{sintT%BT} (load (var 0)))))
                   m1 ⇒* S -> ¬ is_undef_state S).
2: apply H; assumption.
clear H0; intros.
assert (m1_valid: ✓{Γ} m1). {
  apply mem_alloc_valid' with (τ:=sintT%T).
  - apply Γ_valid.
  - apply cmap_empty_valid'.
  - unfold dom.
    unfold cmap_dom.
    simpl.
    rewrite dom_empty_L.
    apply not_elem_of_empty.
  - apply perm_full_valid.
  - apply perm_full_mapped.
  - rewrite val_new_base. simpl.
    apply VBase_typed.
    constructor.
    + constructor.
    + congruence.
}
assert (typeof_o: '{m1} !! o = Some (sintT%T, false)). {
  unfold m1.
  rewrite mem_alloc_memenv_of with (Δ:=∅) (τ:=sintT%T).
  - rewrite lookup_insert. reflexivity.
  - apply Γ_valid.
  - apply val_new_typed.
    + apply Γ_valid.
    + constructor.
      constructor.
}
assert (a_typed: (Γ, '{m1}) ⊢ addr_top o sintT%BT : sintT%PT). {
  constructor.
  - unfold typed.
    unfold index_typed.
    exists false.
    apply typeof_o.
  - constructor.
    constructor.
  - constructor.
  - reflexivity.
  - constructor.
    simpl.
    lia.
  - apply Nat.divide_0_r.
  - constructor.
}
assert (a_writable: mem_writable Γ (addr_top o sintT%BT) m1). {
  apply mem_alloc_writable_top with (Δ:=∅).
  - apply Γ_valid.
  - rewrite val_new_base. simpl.
    apply VBase_typed.
    constructor.
    + constructor.
    + congruence.
  - rewrite perm_kind_full.
    reflexivity.
}
assert (intV_3_typed: (Γ, '{m1}) ⊢ (intV{sintT} 3 : val K) : (sintT%BT : type K)). {
  apply VBase_typed.
  constructor.
  constructor.
  - unfold int_lower. simpl.
    lia.
  - unfold int_upper. simpl. lia.
}
inv_rcsteps H. {
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
unfold int_cast in H.
unfold arch_int_env in H.
unfold int_pre_cast in H.
simpl in H.
inversion H; clear H; subst. {
  inversion 1.
  elim (is_Some_None H).
}
inv_rcstep; clear y.
Focus 2. {
  elim H1; clear H0 H1 H2.
  eapply ehsafe_step.
  constructor.
  - assumption.
  - constructor.
    + constructor.
      * unfold int_lower.
        simpl.
        lia.
      * unfold int_upper.
        unfold int_precision.
        simpl.
        lia.
    + reflexivity.
}
Unfocus.
inv_ehstep.
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
rewrite lockset_union_right_id in H1.
rewrite lockset_union_right_id in H1.
set (m2:=<[addr_top o sintT%BT:=intV{sintT} 3]{Γ}>m1).
assert (Γ\ δ\ [] ⊢ₛ State
                 [CStmt (□ ;; ret (cast{sintT%BT} (load (var 0))));
                 CLocal o sintT%BT; CParams "main" []]
                 (Stmt ↗ (var 0 ::= cast{sintT%BT} (# intV{sintT} 3)))
                 (mem_unlock (lock_singleton Γ (addr_top o sintT%BT))
                    (mem_lock Γ (addr_top o sintT%BT)
                       m2)) ⇒* S).
exact H1.
clear H1.
assert (m2_valid: ✓{Γ} m2). {
  apply mem_insert_valid' with (τ:=sintT%T).
  - apply Γ_valid.
  - apply m1_valid.
  - apply a_typed.
  - apply a_writable.
  - apply intV_3_typed.
}
assert (typeof_o_m2: '{m2} !! o = Some (sintT%T, false)). {
  unfold m2.
  rewrite mem_insert_memenv_of with (Δ:='{m1}) (τ:=sintT%T).
  - apply typeof_o.
  - apply Γ_valid.
  - apply m1_valid.
  - apply a_typed.
  - apply a_writable.
  - apply intV_3_typed.
}
assert (a_writable_m2: mem_writable Γ (addr_top o sintT%BT) m2). {
  unfold m2.
  apply mem_insert_writable with (Δ:='{m1}) (τ2:=sintT%T); try assumption.
  - apply Γ_valid.
  - left; reflexivity.
}
rewrite mem_unlock_lock_singleton in H; try assumption.
inv_rcsteps H. {
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
eapply Expr_pure' with (1:=H1); clear H1. {
  simpl.
  rewrite option_guard_True.
  + unfold m2.
    simpl.
    rewrite mem_lookup_insert with (Δ:='{m1}) (τ:=sintT%T); try assumption.
    * simpl.
      reflexivity.
    * apply Γ_valid.
    * constructor.
  + apply mem_insert_forced.
}
intros.
unfold int_cast in H.
unfold arch_int_env in H.
unfold int_pre_cast in H.
simpl in H.
inv_rcsteps H. {
  inversion 1.
  elim (is_Some_None H).
}
inv_rcstep.
rewrite mem_unlock_empty in H1.
inv_rcsteps H1. {
  inversion 1.
  elim (is_Some_None H).
}
inv_rcstep.
inv_rcsteps H1. {
  inversion 1.
  elim (is_Some_None H).
}
inv_rcstep.
  inv_rcsteps H1. {
  inversion 1.
  elim (is_Some_None H).
}
inv_rcstep.
inv_rcsteps H1. {
  inversion 1.
  elim (is_Some_None H).
}
inv_rcstep.
Qed.

Goal forall S, rtc (cstep Γ δ) S0 S -> ~ is_undef_state S.
intros.
apply call_main_safe with (1:=H).
Qed.
