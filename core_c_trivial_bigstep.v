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

Notation store := (list (option Z)).

Inductive stack_mem `{Env K} (Γ : env K) (Δ : memenv K): stack K -> store -> mem K -> Prop :=
| stack_mem_empty:
  ✓ Γ ->
  ✓{Γ} Δ ->
  stack_mem Γ Δ [] [] ∅
| stack_mem_alloc o mv m ρ st m':
  ✓ Γ ->
  ✓{Γ} Δ ->
  ✓{Γ, Δ} (m ∪ m') ->
  mem_singleton Γ Δ (addr_top o sintT%T) false perm_full
    (match mv with None => indetV sintT%BT | Some z => intV{sintT} z end)
    sintT%T m ->
  stack_mem Γ Δ ρ st m' ->
  ⊥[m; m'] ->
  stack_mem Γ Δ ((o, sintT%T)::ρ) (mv::st) (m ∪ m')
.

Lemma stack_mem_erase `{EnvSpec K} Γ Δ ρ st m:
  stack_mem Γ Δ ρ st m ->
  cmap_erase m = m.
induction 1.
- apply cmap_erase_empty.
- rewrite cmap_erase_union.
  rewrite mem_erase_singleton with (1:=H4).
  rewrite IHstack_mem.
  reflexivity.
Qed.

Definition stack_mem' `{Env K} Γ ρ st m :=
  ✓{Γ} m /\ stack_mem Γ '{m} ρ st (cmap_erase m).

Lemma stack_mem_valid `{EnvSpec K} Γ Δ ρ st m:
  stack_mem Γ Δ ρ st m ->
  ✓{Γ, Δ} m.
induction 1.
- apply cmap_empty_valid.
  assumption.
- assumption.
Qed.

Lemma stack_mem_lookup_stack `{Env K} Γ Δ ρ st m i mv:
  stack_mem Γ Δ ρ st m ->
  st !! i = Some mv ->
  exists o, ρ !! i = Some (o, sintT%T).
intro.
revert i mv.
induction H0.
- intros.
  discriminate.
- intros.
  destruct i.
  + exists o. reflexivity.
  + simpl in H6.
    simpl.
    apply IHstack_mem with (1:=H6).
Qed.

Lemma stack_mem_lookup_mem `{EnvSpec K} Γ Δ ρ st m i v o:
  stack_mem Γ Δ ρ st m ->
  st !! i = Some (Some v) ->
  ρ !! i = Some (o, sintT%T) ->
  m !!{Γ} addr_top o sintT%T = Some (intV{sintT} v).
intro.
revert i v o.
induction H1; intros. {
  discriminate.
}
destruct i; simpl in *.
- injection H7; clear H7; intros; subst.
  injection H8; clear H8; intros; subst.
  eapply mem_lookup_subseteq with (m1:=m).
  + assumption.
  + apply cmap_valid_subseteq with (2:=H3).
    * assumption.
    * apply sep_union_subseteq_l.
      assumption.
  + apply sep_union_subseteq_l.
    assumption.
  + apply mem_lookup_singleton with (3:=H4).
    * assumption.
    * rewrite perm_kind_full.
      reflexivity.
- eapply mem_lookup_subseteq with (m1:=m').
  + assumption.
  + apply stack_mem_valid with (1:=H5).
  + apply sep_union_subseteq_r.
    assumption.
  + apply IHstack_mem with (1:=H7) (2:=H8).
Qed.

Lemma stack_mem_weaken_memenv `{EnvSpec K} Γ Δ ρ st m Δ':
  stack_mem Γ Δ ρ st m ->
  ✓{Γ} Δ' ->
  Δ ⊆ Δ' ->
  stack_mem Γ Δ' ρ st m.
induction 1; intros.
- apply stack_mem_empty; try assumption.
- apply stack_mem_alloc; try assumption.
  + apply cmap_valid_weaken with (2:=H3); trivial.
  + apply mem_singleton_weaken with (4:=H4); try assumption.
    * reflexivity.
    * apply memenv_subseteq_forward.
      assumption.
  + apply IHstack_mem; assumption.
Qed.

Lemma stack_mem_forced `{EnvSpec K} Γ Δ ρ st m i v o:
  stack_mem Γ Δ ρ st m ->
  st !! i = Some (Some v) ->
  ρ !! i = Some (o, sintT%T) ->
  mem_forced Γ (addr_top o sintT%T) m.
intro.
revert i v o.
induction H1; intros. {
  discriminate.
}
destruct i; simpl in *.
- injection H7; clear H7; intros; subst.
  injection H8; clear H8; intros; subst.
  eapply mem_forced_subseteq with (m1:=m); try eassumption.
  + apply cmap_valid_subseteq with (2:=H3).
    * assumption.
    * apply sep_union_subseteq_l.
      assumption.
  + apply sep_union_subseteq_l. assumption.
  + apply mem_singleton_forced with (3:=H4).
    * assumption.
    * rewrite perm_kind_full.
      reflexivity.
  + rewrite mem_lookup_singleton with (3:=H4).
    * unfold is_Some.
      eexists. reflexivity.
    * assumption.
    * rewrite perm_kind_full. reflexivity.
- eapply mem_forced_subseteq with (m1:=m').
  + assumption.
  + apply stack_mem_valid with (1:=H5).
  + apply sep_union_subseteq_r.
    assumption.
  + eapply IHstack_mem; eassumption.
  + rewrite stack_mem_lookup_mem with (1:=H5) (2:=H7) (3:=H8).
    eexists; reflexivity.
Qed.

Lemma stack_mem_free `{EnvSpec K} Γ Δ ρ st m Δ':
  stack_mem Γ Δ ρ st m ->
  memenv_forward Δ Δ' ->
  ✓{Γ, Δ'} m ->
  stack_mem Γ Δ' ρ st m.
induction 1; intros.
- apply stack_mem_empty.
  + assumption.
  + apply cmap_valid_memenv_valid with (1:=H4).
- apply stack_mem_alloc.
  + assumption.
  + apply cmap_valid_memenv_valid with (1:=H8).
  + assumption.
  + apply mem_singleton_weaken with (4:=H4); try assumption.
    * reflexivity.
  + apply IHstack_mem; try assumption.
    * apply cmap_valid_subseteq with (2:=H8).
      -- assumption.
      -- apply sep_union_subseteq_r.
         assumption.
  + assumption.
Qed.

Inductive eval `{Env K}: store -> expr K -> Z -> Prop :=
| eval_lit st z:
  eval st (# intV{sintT} z) z
| eval_load_var st i z:
  st !! i = Some (Some z) ->
  eval st (load (var i)) z
.

Lemma eval_sound `{EnvSpec K} (Γ: env K) st e z ρ m:
  eval st e z ->
  stack_mem Γ '{m} ρ st (cmap_erase m) ->
  ⟦ e ⟧ Γ ρ m = Some (inr (intV{sintT} z)).
intros.
destruct H1.
- (* eval_lit *)
  reflexivity.
- (* eval_load_var *)
  simpl.
  pose proof (stack_mem_lookup_stack _ _ _ _ _ _ _ H2 H1).
  destruct H3 as [o Ho].
  rewrite Ho.
  simpl.
  rewrite option_guard_True.
  + rewrite <- mem_lookup_erase.
    rewrite stack_mem_lookup_mem with (1:=H2) (2:=H1) (3:=Ho).
    reflexivity.
  + rewrite <- mem_forced_erase.
    apply stack_mem_forced with (1:=H2) (2:=H1) (3:=Ho).
Qed.

Inductive outcome := onormal(s: store) | oreturn(z: Z).

Inductive exec `{Env K}: store -> stmt K -> outcome -> Prop :=
| exec_local_normal st s mv st':
  exec (None::st) s (onormal (mv::st')) ->
  exec st (local{sintT%BT} s) (onormal st')
| exec_local_return st s z:
  exec (None::st) s (oreturn z) ->
  exec st (local{sintT%BT} s) (oreturn z)
| exec_assign st i e z:
  i < length st ->
  eval st e z ->
  int_cast_ok sintT z ->
  exec st (var i ::= cast{sintT%BT} e) (onormal (<[i:=Some z]>st))
| exec_seq st s1 st' s2 O:
  exec st s1 (onormal st') ->
  exec st' s2 O ->
  exec st (s1 ;; s2) O
| exec_ret st e z:
  eval st e z ->
  int_cast_ok sintT z ->
  exec st (ret (cast{sintT%BT} e)) (oreturn z)
.

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

Lemma stack_mem_typed `{EnvSpec K} Γ Δ ρ st m i o:
  stack_mem Γ Δ ρ st m ->
  ρ !! i = Some (o, sintT%T) ->
  (Γ, Δ) ⊢ addr_top o sintT%BT : sintT%PT.
intro.
revert i.
induction H1; intros.
- discriminate.
- destruct i.
  + simpl in *.
    injection H7; clear H7; intros; subst.
    apply mem_singleton_typed_addr_typed with (1:=H4).
  + simpl in H7.
    apply IHstack_mem with (1:=H7).
Qed.

Lemma stack_mem_writable `{EnvSpec K} Γ Δ ρ st m i o:
  stack_mem Γ Δ ρ st m ->
  ρ !! i = Some (o, sintT%T) ->
  mem_writable Γ (addr_top o sintT%BT) m.
intro.
revert i.
induction H1; intros.
- discriminate.
- destruct i; simpl in H7.
  + injection H7; clear H7; intros; subst.
    eapply mem_writable_subseteq.
    * assumption.
    * apply cmap_valid_subseteq with (2:=H3).
      -- assumption.
      -- apply sep_union_subseteq_l.
         assumption.
    * apply sep_union_subseteq_l; assumption.
    * apply mem_writable_singleton with (3:=H4).
      -- assumption.
      -- reflexivity.
  + eapply mem_writable_subseteq.
    * assumption.
    * apply cmap_valid_subseteq with (2:=H3).
      -- assumption.
      -- apply sep_union_subseteq_r.
         assumption.
    * apply sep_union_subseteq_r; assumption.
    * apply IHstack_mem with (1:=H7).
Qed.

Lemma stack_mem_insert `{EnvSpec K} Γ Δ ρ st m i o z:
  stack_mem Γ Δ ρ st m ->
  ρ !! i = Some (o, sintT%T) ->
  int_typed z sintT ->
  cmap_valid (Γ, Δ) (<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m) ->
  stack_mem Γ Δ ρ (<[i:=Some z]> st)
    (<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m).
intro.
revert i.
induction H1; intros.
- discriminate.
- destruct i.
  + simpl in H7.
    injection H7; clear H7; intros; subst.
    assert (<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m ⊥ m'). {
            apply mem_insert_disjoint with (Δ1:=Δ) (τ1:=sintT%T).
            ** assumption.
            ** apply cmap_valid_subseteq with (2:=H3).
               --- assumption.
               --- apply sep_union_subseteq_l; assumption.
            ** rewrite sep_disjoint_list_double in H6.
               assumption.
            ** apply mem_singleton_typed_addr_typed with (1:=H4).
            ** apply mem_writable_singleton with (3:=H4).
               --- assumption.
               --- reflexivity.
            ** constructor.
               constructor.
               assumption.
    }
    assert (Hunion: <[addr_top o sintT%BT:=intV{sintT} z]{Γ}> (m ∪ m') = <[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m ∪ m'). {
      apply mem_insert_union with (Δ1:=Δ) (τ1:=sintT%T).
         ++ assumption.
         ++ apply cmap_valid_subseteq with (2:=H3).
            +++ assumption.
            +++ apply sep_union_subseteq_l; assumption.
         ++ rewrite sep_disjoint_list_double in H6; assumption.
         ++ apply mem_singleton_typed_addr_typed with (1:=H4).
         ++ apply mem_writable_singleton with (3:=H4).
                   +++ assumption.
                   +++ reflexivity.
         ++ constructor; constructor; assumption.
    }
    rewrite Hunion.
    * apply stack_mem_alloc.
      -- assumption.
      -- assumption.
      -- rewrite Hunion in H9; assumption.
      -- assert (Hz: intV{sintT} z = freeze true (intV{sintT} z)). reflexivity.
         rewrite Hz at 1.
         apply mem_insert_singleton with (3:=H4).
         ++ assumption.
         ++ reflexivity.
         ++ constructor; constructor; assumption.
      -- assumption.
      -- rewrite sep_disjoint_list_double; assumption.
  + simpl in H7.
    assert (Hdisjoint: ⊥ [<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m'; m]). {
      apply sep_disjoint_list_double.
      apply mem_insert_disjoint with (Δ1:=Δ) (τ1:=sintT%T).
      - assumption.
      - apply cmap_valid_subseteq with (2:=H3).
            +++ assumption.
            +++ apply sep_union_subseteq_r; assumption.
      - apply symmetry.
        rewrite sep_disjoint_list_double in H6; assumption.
      - apply stack_mem_typed with (1:=H5) (2:=H7).
      - apply stack_mem_writable with (1:=H5) (2:=H7).
      - constructor; constructor; assumption.
    }
    assert (Hunion: <[addr_top o sintT%BT:=intV{sintT} z]{Γ}> (m ∪ m') = m ∪ <[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m'). {
      rewrite sep_commutative. 2:assumption.
      rewrite mem_insert_union with (Δ1:=Δ) (τ1:=sintT%T).
         ++ apply sep_commutative. assumption.
         ++ assumption.
         ++ apply cmap_valid_subseteq with (2:=H3).
            +++ assumption.
            +++ apply sep_union_subseteq_r; assumption.
         ++ apply symmetry; rewrite sep_disjoint_list_double in H6; assumption.
         ++ apply stack_mem_typed with (1:=H5) (2:=H7).
         ++ apply stack_mem_writable with (1:=H5) (2:=H7).
         ++ constructor; constructor; assumption.
    }
    rewrite Hunion.
    * apply stack_mem_alloc.
      -- assumption.
      -- assumption.
      -- rewrite Hunion in H9; assumption.
      -- assumption.
      -- apply IHstack_mem; try assumption.
         apply cmap_valid_subseteq with (2:=H9); try assumption.
         rewrite Hunion.
         apply sep_union_subseteq_r.
         rewrite sep_disjoint_list_double.
         rewrite sep_disjoint_list_double in Hdisjoint.
         apply symmetry; assumption.
      -- rewrite sep_disjoint_list_double.
         rewrite sep_disjoint_list_double in Hdisjoint.
         apply symmetry; assumption.
Qed.

Lemma bigstep_sound_lemma (Γ: env K) δ st s O S (P: Prop):
  ✓ Γ ->
  is_final_state S ->
  exec st s O ->
  forall k m,
  Γ\ δ\ [] ⊢ₛ State k (Stmt ↘ s) m ⇒* S ->
  stack_mem' Γ (rlocals [] k) st m ->
  (forall st' m',
   O = onormal st' ->
   stack_mem' Γ (rlocals [] k) st' m' ->
   Γ\ δ\ [] ⊢ₛ State k (Stmt ↗ s) m' ⇒* S ->
   P) ->
  (forall z m',
   O = oreturn z ->
   Γ\ δ\ [] ⊢ₛ State k (Stmt (⇈ intV{sintT} z) s) m' ⇒* S ->
   P) ->
  P.
assert (H: True). exact I.
assert (H0: True). exact I.
intros HΓ HS.
induction 1.
- (* exec_local_normal *)
  intros.
  inv_rcsteps H2. {
    elim HS.
  }
  inv_rcstep.
  apply IHexec with (1:=H7).
  + simpl.
    unfold stack_mem' in *.
    destruct H3 as [Hvalid H3].
    assert (Hval_new: val_new Γ sintT%BT = indetV sintT). {
      rewrite val_new_base.
      destruct (decide (sintT%BT = voidT%BT)); try discriminate.
      reflexivity.
    }
    rewrite <- Hint_coding in *.
    rewrite Hval_new in *.
    assert (Halloc_valid: ✓{Γ} (mem_alloc Γ o false perm_full (indetV sintT%BT) m)). {
      apply mem_alloc_valid' with (τ:=sintT%T).
      - assumption.
      - assumption.
      - assumption.
      - apply perm_full_valid.
      - apply perm_full_mapped.
      - constructor. constructor.
        + constructor.
        + discriminate.
    }
    destruct (mem_alloc_singleton Γ '{mem_alloc Γ o false perm_full (indetV sintT%BT) m} (cmap_erase m) o false perm_full (indetV sintT) sintT%T) as [m2 [Hmem_alloc [Hdisjoint Hsingleton]]].
    * assumption.
    * apply cmap_erase_valid.
      -- apply cmap_valid_weaken with (Γ1:=Γ) (Δ1:='{m}).
         ++ assumption.
         ++ assumption.
         ++ reflexivity.
         ++ rewrite mem_alloc_memenv_of with (Δ:='{m}) (τ:=sintT%T).
            ** apply insert_subseteq.
               rewrite <- cmap_dom_memenv_of in H2.
                apply not_elem_of_dom with (1:=H2).
            ** assumption.
            ** constructor. constructor.
               --- constructor.
               --- discriminate.
         ++ eapply cmap_valid_memenv_valid.
            eassumption.
    * rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
      -- apply mem_alloc_index_typed.
      -- assumption.
      -- constructor. constructor.
         ++ constructor.
         ++ discriminate.
    * rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
      -- apply mem_alloc_index_alive.
      -- assumption.
      -- constructor. constructor.
         ++ constructor.
         ++ discriminate.
    * intro.
      apply cmap_dom_erase in H6.
      tauto.
    * apply perm_full_valid.
    * apply perm_full_mapped.
    * constructor. constructor.
      -- constructor.
      -- discriminate.
    * split. {
        apply mem_alloc_valid' with (τ:=sintT%T).
        - assumption.
        - assumption.
        - assumption.
        - apply perm_full_valid.
        - apply perm_full_mapped.
        - constructor. constructor.
          + constructor.
          + discriminate.
      }
      rewrite mem_erase_alloc.
      rewrite Hint_coding.
      rewrite Hmem_alloc.
      apply stack_mem_alloc.
      -- assumption.
      -- eapply cmap_valid_memenv_valid; eassumption.
      -- rewrite <- Hmem_alloc.
         rewrite <- mem_erase_alloc.
         apply cmap_erase_valid.
         assumption.
      -- assumption.
      -- apply stack_mem_weaken_memenv with (Δ:='{m}).
         ++ assumption.
         ++ eapply cmap_valid_memenv_valid; eassumption.
         ++ rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
            ** apply insert_subseteq.
               rewrite <- cmap_dom_memenv_of in H2.
               apply not_elem_of_dom with (1:=H2).
            ** assumption.
            ** constructor.
               constructor.
               --- constructor.
               --- discriminate.
      -- apply sep_disjoint_list_double; assumption.
  + intros.
    injection H6; clear H6; intros; subst.
    simpl in *.
    inv_rcsteps H9. {
      elim HS.
    }
    inv_rcstep.
    apply H4 with (st'0:=st') (3:=H10).
    * reflexivity.
    * destruct H8 as [H8' H8].
      inversion H8; subst.
      split.
      -- apply mem_free_valid'.
         ++ assumption.
         ++ assumption.
      -- rewrite mem_erase_free.
         rewrite <- H13.
         assert (Hfree_union: mem_free o (m0 ∪ m'0) = mem_free o m0 ∪ m'0). {
           apply mem_free_union with (μ:=false).
           - rewrite sep_disjoint_list_double in H19; assumption.
           - apply mem_freeable_perm_singleton with (1:=H17).
         }
         rewrite Hfree_union.
         ++ rewrite cmap_erase_union.
            rewrite mem_free_singleton with (1:=H17). 2: reflexivity.
            rewrite sep_left_id.
            rewrite stack_mem_erase with (1:=H18).
            apply stack_mem_free with (1:=H18).
            ** rewrite mem_free_memenv_of.
               apply mem_free_forward.
            ** apply cmap_valid_subseteq with (m2:=cmap_erase (mem_free o m')).
               --- assumption.
               --- apply cmap_erase_valid. apply mem_free_valid'; assumption.
               --- rewrite mem_erase_free.
                   rewrite <- H13.
                   rewrite Hfree_union.
                   rewrite cmap_erase_union.
                   rewrite stack_mem_erase with (1:=H18).
                   apply sep_union_subseteq_r.
                   apply sep_disjoint_list_double.
                   rewrite mem_free_singleton with (1:=H17).
                   +++ apply sep_disjoint_empty_l.
                       eapply cmap_valid_sep_valid; eapply stack_mem_valid with (1:=H18).
                   +++ reflexivity.
            ** eapply cmap_valid_sep_valid; rewrite stack_mem_erase with (1:=H18); apply stack_mem_valid with (1:=H18).
  + intros; discriminate.
- (* exec_local_return *)
  intros.
  inv_rcsteps H2. {
    elim HS.
  }
  inv_rcstep.
  apply IHexec with (1:=H7).
  + simpl.
    unfold stack_mem' in *.
    destruct H3 as [Hvalid H3].
    assert (Hval_new: val_new Γ sintT%BT = indetV sintT). {
      rewrite val_new_base.
      destruct (decide (sintT%BT = voidT%BT)); try discriminate.
      reflexivity.
    }
    rewrite Hint_coding.
    rewrite Hval_new in *.
    assert (Halloc_valid: ✓{Γ} (mem_alloc Γ o false perm_full (indetV sintT%BT) m)). {
      apply mem_alloc_valid' with (τ:=sintT%T).
      - assumption.
      - assumption.
      - assumption.
      - apply perm_full_valid.
      - apply perm_full_mapped.
      - constructor. constructor.
        + constructor.
        + discriminate.
    }
    destruct (mem_alloc_singleton Γ '{mem_alloc Γ o false perm_full (indetV sintT%BT) m} (cmap_erase m) o false perm_full (indetV sintT) sintT%T) as [m2 [Hmem_alloc [Hdisjoint Hsingleton]]].
    * assumption.
    * apply cmap_erase_valid.
      -- apply cmap_valid_weaken with (Γ1:=Γ) (Δ1:='{m}).
         ++ assumption.
         ++ assumption.
         ++ reflexivity.
         ++ rewrite mem_alloc_memenv_of with (Δ:='{m}) (τ:=sintT%T).
            ** apply insert_subseteq.
               rewrite <- cmap_dom_memenv_of in H2.
                apply not_elem_of_dom with (1:=H2).
            ** assumption.
            ** constructor. constructor.
               --- constructor.
               --- discriminate.
         ++ eapply cmap_valid_memenv_valid.
            eassumption.
    * rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
      -- apply mem_alloc_index_typed.
      -- assumption.
      -- constructor. constructor.
         ++ constructor.
         ++ discriminate.
    * rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
      -- apply mem_alloc_index_alive.
      -- assumption.
      -- constructor. constructor.
         ++ constructor.
         ++ discriminate.
    * intro.
      apply cmap_dom_erase in H6.
      tauto.
    * apply perm_full_valid.
    * apply perm_full_mapped.
    * constructor. constructor.
      -- constructor.
      -- discriminate.
    * split. {
        apply mem_alloc_valid' with (τ:=sintT%T).
        - assumption.
        - assumption.
        - assumption.
        - apply perm_full_valid.
        - apply perm_full_mapped.
        - constructor. constructor.
          + constructor.
          + discriminate.
      }
      rewrite mem_erase_alloc.
      rewrite Hmem_alloc.
      apply stack_mem_alloc.
      -- assumption.
      -- eapply cmap_valid_memenv_valid; eassumption.
      -- rewrite <- Hmem_alloc.
         rewrite <- mem_erase_alloc.
         apply cmap_erase_valid.
         assumption.
      -- assumption.
      -- apply stack_mem_weaken_memenv with (Δ:='{m}).
         ++ assumption.
         ++ eapply cmap_valid_memenv_valid; eassumption.
         ++ rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
            ** apply insert_subseteq.
               rewrite <- cmap_dom_memenv_of in H2.
               apply not_elem_of_dom with (1:=H2).
            ** assumption.
            ** constructor.
               constructor.
               --- constructor.
               --- discriminate.
      -- apply sep_disjoint_list_double; assumption.
  + intros; discriminate.
  + intros.
    injection H6; clear H6; intros; subst.
    simpl in *.
    inv_rcsteps H8. {
      elim HS.
    }
    inv_rcstep.
    apply H5 with (z:=z0) (2:=H9).
    reflexivity.
- (* exec_assign *)
  intros.
  inv_rcsteps H4. {
    elim HS.
  }
  inv_rcstep.
  clear y.
  destruct (lookup_lt_is_Some_2 _ _ H1) as [mv Hmv].
  destruct H5 as [Hvalid H5].
  destruct (stack_mem_lookup_stack _ _ _ _ _ _ _ H5 Hmv) as [o Ho].
  eapply assign_pure' with (1:=H9).
  + assumption.
  + simpl.
    rewrite Ho.
    simpl.
    reflexivity.
  + simpl.
    rewrite eval_sound with (1:=H2). 2:assumption.
    simpl.
    rewrite option_guard_True.
    * reflexivity.
    * assumption.
  + intros.
    unfold int_cast in H4.
    unfold arch_int_env in H4.
    unfold int_pre_cast in H4.
    simpl in H4.
    inv_rcsteps H4. {
      elim HS.
    }
    inv_rcstep.
    inversion H8; subst.
    * clear H8.
      rewrite lockset_union_right_id in H10.
      rewrite lockset_union_right_id in H10.
      inv_rcsteps H10. {
        elim HS.
      }
      inv_rcstep.
      inversion H19; subst.
      simpl in H10.
      unfold int_cast in H10.
      unfold arch_int_env in H10.
      unfold int_pre_cast in H10.
      simpl in H10.
      assert ((Γ, '{m}) ⊢ addr_top o sintT%BT : sintT%PT). {
        apply stack_mem_typed with (1:=H5) (2:=Ho).
      }
      assert (Hz_typed: (Γ, '{m}) ⊢ (intV{sintT} z: val K) : (sintT%BT: type K)). {
        constructor.
        constructor.
        inversion H3.
        constructor; assumption.
      }
      assert (Hinsert_valid: ✓{Γ} (<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m)). {
        apply mem_insert_valid' with (τ:=sintT%T); assumption.
      }
      assert (✓{Γ} (<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m)). {
        apply mem_insert_valid' with (τ:=sintT%T); assumption.
      }
      rewrite mem_unlock_lock_singleton in H10; try assumption.
      -- apply H6 with (3:=H10) (st':=<[i:=Some z]>st).
         ++ reflexivity.
         ++ split.
            ** assumption.
            ** assert ('{<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m} = '{m}). {
                 rewrite mem_insert_memenv_of with (Δ:='{m}) (τ:=sintT%T); try assumption.
                 - reflexivity.
               }
               rewrite Hint_coding.
               rewrite H12.
               rewrite mem_erase_insert.
               apply stack_mem_insert.
               +++ assumption.
               +++ assumption.
               +++ assumption.
               +++ assert (✓{Γ, '{(<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m)}} (<[addr_top o sintT%BT:=intV{sintT} z]{Γ}> m)). {
                         assumption.
                   }
                   rewrite <- H12.
                   rewrite <- mem_erase_insert.
                   apply cmap_erase_valid.
                   assumption.
      -- rewrite mem_insert_memenv_of with (Δ:='{m}) (τ:=sintT%T); try assumption.
      -- apply mem_insert_writable with (Δ:='{m}) (τ2:=sintT%T); try assumption.
         ++ left; reflexivity.
    * elim H10.
      eapply ehsafe_step.
      constructor.
      -- rewrite <- mem_erase_writable. apply stack_mem_writable with (1:=H5) (2:=Ho).
      -- constructor.
         ++ assumption.
         ++ reflexivity.
- intros.
  inv_rcsteps H1. {
    elim HS.
  }
  inv_rcstep.
  apply IHexec1 with (1:=H6) (2:=H2); intros.
  + inv_rcsteps H7. elim HS. inv_rcstep.
    simpl in *.
    apply IHexec2 with (1:=H9) (2:=H5); intros.
    * inv_rcsteps H8. elim HS. inv_rcstep.
      apply H3 with (2:=H7); trivial.
    * inv_rcsteps H7. elim HS. inv_rcstep.
      eapply H4. reflexivity. eassumption.
  + inv_rcsteps H5. elim HS. inv_rcstep.
- intros.
  inv_rcsteps H3. elim HS. inv_rcstep.
  eapply Expr_pure' in H8; try assumption.
  Focus 2. {
    simpl.
    rewrite eval_sound with (1:=H1).
    - simpl.
      rewrite option_guard_True. reflexivity.
      assumption.
    - destruct H4; assumption.
  } Unfocus.
  inv_rcsteps H8. elim HS. inv_rcstep.
  rewrite mem_unlock_empty in H8.
  unfold int_cast in H8.
  unfold arch_int_env in H8.
  unfold int_pre_cast in H8.
  simpl in H8.
  eapply H6 with (2:=H8).
  reflexivity.
Qed.

Theorem bigstep_sound Γ δ (s: stmt K) z S:
  ✓ Γ ->
  exec [] s (oreturn z) ->
  is_final_state S ->
  Γ\ δ\ [] ⊢ₛ State [] (Stmt ↘ s) ∅ ⇒* S ->
  exists m,
  S = State [] (Stmt (⇈ (intV{sintT} z)) s) m.
intros.
apply bigstep_sound_lemma with (1:=H) (2:=H1) (3:=H0) (4:=H2).
- split.
  + apply cmap_empty_valid.
    simpl.
    rewrite fmap_empty.
    apply memenv_empty_valid.
  + rewrite cmap_erase_empty.
    apply stack_mem_empty.
    * assumption.
    * simpl. rewrite fmap_empty.
      apply memenv_empty_valid.
- intros.
  inv_rcsteps H5. elim H1. inv_rcstep.
- intros.
  injection H3; clear H3; intros; subst.
  inv_rcsteps H4.
  + exists m'; reflexivity.
  + inv_rcstep.
Qed.
