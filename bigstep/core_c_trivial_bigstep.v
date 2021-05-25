Require Export stack_memory.
Require Export restricted_smallstep_lemmas.

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

Lemma exec_sound_lemma (Γ: env K) δ st s O S (P: Prop):
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

Theorem exec_sound Γ δ (s: stmt K) z S f:
  ✓ Γ ->
  exec [] s (oreturn z) ->
  is_final_state S ->
  Γ\ δ\ [] ⊢ₛ State [CParams f []] (Stmt ↘ s) ∅ ⇒* S ->
  exists m,
  Γ\ δ\ [] ⊢ₛ State [CParams f []] (Stmt (⇈ (intV{sintT} z)) s) m ⇒* S.
intros.
apply exec_sound_lemma with (1:=H) (2:=H1) (3:=H0) (4:=H2).
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
  eexists; eassumption.
Qed.
