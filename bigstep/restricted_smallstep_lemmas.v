Require Export ZArith.
Require Export ch2o.core_c.expressions.
Require Export ch2o.memory_separation.memory_singleton.
Require Export ch2o.separation.permissions.
Require Export ch2o.core_c.expressions.
Require Export ch2o.core_c.expression_eval.
Require Export ch2o.core_c.restricted_smallstep.
Require Export ch2o.core_c.expression_eval_smallstep.
Require Export ch2o.abstract_c.natural_type_environment.
Require Export ch2o.abstract_c.architecture_spec.
Require Export ch2o.abstract_c.architectures.

Definition is_final_state `{Env K} (S: state K) :=
  match S with
    State _ (Return _ _) _ => True
  | State _ (Undef _) _ => True
  | _ => False
  end.

Lemma mem_erase_free `{EnvSpec K} o (m: mem K):
  cmap_erase (mem_free o m) = cmap_erase (mem_free o (cmap_erase m)).
destruct m as [m].
unfold cmap_erase.
unfold mem_free.
assert (forall m1 m2, m1 = m2 -> (CMap m1: mem K) = CMap m2). intros; congruence.
apply H1.
apply map_eq.
intros.
rewrite lookup_omap.
rewrite lookup_omap.
destruct (decide (o = i)).
- subst.
  rewrite lookup_alter.
  rewrite lookup_alter.
  rewrite lookup_omap.
  destruct (m !! i).
  + destruct c; reflexivity.
  + reflexivity.
- rewrite lookup_alter_ne with (1:=n).
  rewrite lookup_alter_ne with (1:=n).
  rewrite lookup_omap.
  destruct (m !! i).
  + destruct c; reflexivity.
  + reflexivity.
Qed.

Definition A: architecture := {|
  arch_sizes := architectures.lp64;
  arch_big_endian := false;
  arch_char_signedness := Signed;
  arch_alloc_can_fail := false
|}.
Notation K := (arch_rank A).

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
  (Γ, '{m}) ⊢ addr_top o sintT%BT : sintT%PT ->
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
  unfold typed in H.
  unfold addr_typed in H.
  simpl in H.
  inversion H; clear H; subst.
  unfold typed in H8.
  unfold index_typed in H8.
  destruct H8 as [β Ho].
  rewrite lookup_fmap in Ho.
  rewrite H0 in Ho.
  simpl in Ho.
  injection Ho; clear Ho; intros; subst.
  destruct w; try discriminate.
  destruct b0; try discriminate.
  destruct i; try discriminate.
  simpl in H2.
  injection H2; clear H2; intros; subst.
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
    rewrite H5.
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
  rewrite H2.
  pose proof (zip_with_pbit_unlock_if_list_fmap_pbit_lock l H'w).
  rewrite H0 in H6.
  simpl in H6.
  rewrite H6.
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
  is_final_state S ->
  forall k el er m νl νr,
  S0 = State k (Expr (el ::= er)) m ->
  ⟦ el ⟧ Γ (rlocals ρ k) m = Some νl ->
  ⟦ er ⟧ Γ (rlocals ρ k) m = Some νr ->
  Γ\ δ\ ρ ⊢ₛ State k (Expr (%# νl ::= %# νr)) m ⇒* S.
induction 1; intros; subst. {
  elim H.
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

Lemma assign_pure' (Γ: env K) δ ρ S k el er m νl νr P:
  Γ\ δ\ ρ ⊢ₛ (State k (Expr (el ::= er)) m) ⇒* S ->
  is_final_state S ->
  ⟦ el ⟧ Γ (rlocals ρ k) m = Some νl ->
  ⟦ er ⟧ Γ (rlocals ρ k) m = Some νr ->
  (Γ\ δ\ ρ ⊢ₛ State k (Expr (%# νl ::= %# νr)) m ⇒* S ->
   P) ->
  P.
intros.
apply X.
apply assign_pure with (1:=H) (2:=H0) (4:=H1) (5:=H2).
reflexivity.
Qed.

Lemma Expr_pure (Γ: env K) δ ρ S0 S:
  Γ\ δ\ ρ ⊢ₛ S0 ⇒* S ->
  is_final_state S ->
  forall k e m ν,
  S0 = State k (Expr e) m ->
  ⟦ e ⟧ Γ (rlocals ρ k) m = Some ν ->
  Γ\ δ\ ρ ⊢ₛ State k (Expr (%# ν)) m ⇒* S.
intro Hrtc.
pose proof Hrtc.
induction H; intros; subst. {
  elim H.
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
  is_final_state S ->
  ⟦ e ⟧ Γ (rlocals ρ k) m = Some ν ->
  Γ\ δ\ ρ ⊢ₛ State k (Expr (%# ν)) m ⇒* S.
intros.
apply Expr_pure with (1:=H) (2:=H0) (4:=H1).
reflexivity.
Qed.

Lemma Hint_coding: arch_int_coding A = (@int_coding 
                               (arch_rank A)
                               (@env_type_env 
                                  (arch_rank A) 
                                  (arch_env A))).
reflexivity.
Qed.
