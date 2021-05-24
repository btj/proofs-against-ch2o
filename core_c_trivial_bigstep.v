Require Export ZArith.
Require Export ch2o.core_c.expressions.
Require Export ch2o.memory_separation.memory_singleton.
Require Export ch2o.separation.permissions.
Require Export ch2o.core_c.expressions.
Require Export ch2o.core_c.expression_eval.
Require Export ch2o.core_c.restricted_smallstep.

Notation store := (list (option Z)).

Inductive mem_stack `{Env K} (Γ : env K) (Δ : memenv K): stack K -> store -> mem K -> Prop :=
| mem_stack_empty m:
  ✓ Γ ->
  ✓{Γ} Δ ->
  ✓{Γ, Δ} m ->
  mem_stack Γ Δ [] [] m
| mem_stack_alloc o mv m ρ st m':
  ✓ Γ ->
  ✓{Γ} Δ ->
  ✓{Γ, Δ} (m ∪ m') ->
  mem_singleton Γ Δ (addr_top o sintT%T) false perm_full
    (match mv with None => indetV sintT%BT | Some z => intV{sintT} z end)
    sintT%T m ->
  mem_stack Γ Δ ρ st m' ->
  ⊥[m; m'] ->
  mem_stack Γ Δ ((o, sintT%T)::ρ) (mv::st) (m ∪ m')
| mem_stack_freed ρ st m m':
  ✓ Γ ->
  mem_stack Γ Δ ρ st m ->
  m ⊆ m' ->
  ✓{Γ, Δ} m' ->
  mem_stack Γ Δ ρ st m'
.

Lemma mem_stack_valid `{EnvSpec K} Γ Δ ρ st m:
  mem_stack Γ Δ ρ st m ->
  ✓{Γ, Δ} m.
induction 1.
- assumption.
- assumption.
- assumption.
Qed.

Lemma mem_stack_lookup_stack `{Env K} Γ Δ ρ st m i mv:
  mem_stack Γ Δ ρ st m ->
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
    apply IHmem_stack with (1:=H6).
- apply IHmem_stack.
Qed.

Lemma mem_stack_lookup_mem `{EnvSpec K} Γ Δ ρ st m i v o:
  mem_stack Γ Δ ρ st m ->
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
  + apply mem_stack_valid with (1:=H5).
  + apply sep_union_subseteq_r.
    assumption.
  + apply IHmem_stack with (1:=H7) (2:=H8).
- eapply mem_lookup_subseteq with (m1:=m).
  + assumption.
  + apply mem_stack_valid with (1:=H2).
  + assumption.
  + eapply IHmem_stack; eassumption.
Qed.

Lemma mem_stack_weaken_memenv `{EnvSpec K} Γ Δ ρ st m Δ':
  mem_stack Γ Δ ρ st m ->
  ✓{Γ} Δ' ->
  Δ ⊆ Δ' ->
  mem_stack Γ Δ' ρ st m.
induction 1; intros.
- apply mem_stack_empty; try assumption.
  apply cmap_valid_weaken with (2:=H3); try assumption; try reflexivity.
- apply mem_stack_alloc; try assumption.
  + apply cmap_valid_weaken with (2:=H3); trivial.
  + apply mem_singleton_weaken with (4:=H4); try assumption.
    * reflexivity.
    * apply memenv_subseteq_forward.
      assumption.
  + apply IHmem_stack; assumption.
- apply mem_stack_freed with (m0:=m); auto.
  apply cmap_valid_weaken with (2:=H4); trivial.
Qed.

Lemma mem_stack_forced `{EnvSpec K} Γ Δ ρ st m i v o:
  mem_stack Γ Δ ρ st m ->
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
  + apply mem_stack_valid with (1:=H5).
  + apply sep_union_subseteq_r.
    assumption.
  + eapply IHmem_stack; eassumption.
  + rewrite mem_stack_lookup_mem with (1:=H5) (2:=H7) (3:=H8).
    eexists; reflexivity.
- eapply mem_forced_subseteq with (3:=H3).
  + assumption.
  + apply mem_stack_valid with (1:=H2).
  + eapply IHmem_stack; eassumption.
  + rewrite mem_stack_lookup_mem with (1:=H2) (2:=H5) (3:=H6).
    eexists; reflexivity.
Qed.

Lemma mem_stack_free `{EnvSpec K} Γ Δ ρ st m Δ':
  mem_stack Γ Δ ρ st m ->
  memenv_forward Δ Δ' ->
  ✓{Γ, Δ'} m ->
  mem_stack Γ Δ' ρ st m.
induction 1; intros.
- apply mem_stack_empty.
  + assumption.
  + apply cmap_valid_memenv_valid with (1:=H5).
  + assumption.
- apply mem_stack_alloc.
  + assumption.
  + apply cmap_valid_memenv_valid with (1:=H8).
  + assumption.
  + apply mem_singleton_weaken with (4:=H4); try assumption.
    * reflexivity.
  + apply IHmem_stack; try assumption.
    * apply cmap_valid_subseteq with (2:=H8).
      -- assumption.
      -- apply sep_union_subseteq_r.
         assumption.
  + assumption.
- apply mem_stack_freed with (m0:=m); try assumption.
  apply IHmem_stack; try assumption.
  + apply cmap_valid_subseteq with (2:=H6); assumption.
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
  mem_stack Γ '{m} ρ st m ->
  ⟦ e ⟧ Γ ρ m = Some (inr (intV{sintT} z)).
intros.
destruct H1.
- (* eval_lit *)
  reflexivity.
- (* eval_load_var *)
  simpl.
  pose proof (mem_stack_lookup_stack _ _ _ _ _ _ _ H2 H1).
  destruct H3 as [o Ho].
  rewrite Ho.
  simpl.
  rewrite option_guard_True.
  + rewrite mem_stack_lookup_mem with (1:=H2) (2:=H1) (3:=Ho).
    reflexivity.
  + apply mem_stack_forced with (1:=H2) (2:=H1) (3:=Ho).
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
  eval st e z ->
  exec st (var i ::= cast{sintT%BT} e) (onormal (<[i:=Some z]>st))
| exec_seq st s1 st' s2 O:
  exec st s1 (onormal st') ->
  exec st s2 O ->
  exec st (s1 ;; s2) O
| exec_ret st e z:
  eval st e z ->
  exec st (ret (cast{sintT%BT} e)) (oreturn z)
.

Definition is_final_state `{Env K} (S: state K) :=
  match S with
    State _ (Return _ _) _ => True
  | State _ (Undef _) _ => True
  | _ => False
  end.

Lemma bigstep_sound_lemma `{EnvSpec K} Γ δ st s O S (P: Prop):
  ✓ Γ ->
  is_final_state S ->
  exec st s O ->
  forall k m,
  Γ\ δ\ [] ⊢ₛ State k (Stmt ↘ s) m ⇒* S ->
  mem_stack Γ '{m} (rlocals [] k) st m ->
  (forall st' m',
   O = onormal st' ->
   mem_stack Γ '{m'} (rlocals [] k) st' m' ->
   Γ\ δ\ [] ⊢ₛ State k (Stmt ↗ s) m' ⇒* S ->
   P) ->
  (forall z st' m',
   O = oreturn z ->
   mem_stack Γ '{m'} (rlocals [] k) st' m' ->
   Γ\ δ\ [] ⊢ₛ State k (Stmt (⇈ intV{sintT} z) s) m' ⇒* S ->
   P) ->
  P.
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
    destruct (mem_alloc_singleton Γ '{mem_alloc Γ o false perm_full (val_new Γ sintT%BT) m} m o false perm_full (indetV sintT) sintT%T) as [m2 [Hmem_alloc [Hdisjoint Hsingleton]]].
    * assumption.
    * rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
      -- apply cmap_valid_weaken with (Γ1:=Γ) (Δ1:='{m}).
         ++ assumption.
         ++ apply mem_stack_valid with (1:=H3).
         ++ reflexivity.
         ++ apply insert_subseteq.
            rewrite <- cmap_dom_memenv_of in H2.
            apply not_elem_of_dom with (1:=H2).
         ++ rewrite <- mem_alloc_memenv_of with (Γ0:=Γ) (Δ:=empty) (μ:=false) (γ:=perm_full) (v:=indetV sintT).
            apply mem_alloc_valid' with (τ:=sintT%T).
            ** assumption.
            ** apply mem_stack_valid with (1:=H3).
            ** assumption.
            ** apply perm_full_valid.
            ** apply perm_full_mapped.
            ** constructor. constructor.
               --- constructor.
               --- discriminate.
            ** assumption.
            ** constructor. constructor.
               --- constructor.
               --- discriminate.
      -- assumption.
      -- apply val_new_typed.
         ** assumption.
         ** constructor.
            constructor.
    * rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
      -- apply mem_alloc_index_typed.
      -- assumption.
      -- apply val_new_typed.
         ** assumption.
         ** constructor.
            constructor.
    * rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
      -- apply mem_alloc_index_alive.
      -- assumption.
      -- apply val_new_typed.
         ++ assumption.
         ++ constructor.
            constructor.
    * assumption.
    * apply perm_full_valid.
    * apply perm_full_mapped.
    * constructor. constructor.
      -- constructor.
      -- discriminate.
    * assert (val_new Γ sintT%BT = indetV sintT). {
        rewrite val_new_base.
        destruct (decide (sintT%BT = voidT%BT)); try discriminate.
        reflexivity.
      }
      rewrite H6 in *.
      rewrite Hmem_alloc.
      apply mem_stack_alloc.
      -- assumption.
      -- rewrite <- Hmem_alloc.
         eapply cmap_valid_memenv_valid.
         apply mem_alloc_valid' with (τ:=sintT%T).
         ++ assumption.
         ++ apply mem_stack_valid with (1:=H3).
         ++ assumption.
         ++ apply perm_full_valid.
         ++ apply perm_full_mapped.
         ++ constructor.
            constructor.
            ** constructor.
            ** discriminate.
      -- rewrite <- Hmem_alloc.
         apply mem_alloc_valid' with  (τ:=sintT%T).
         ++ assumption.
         ++ apply mem_stack_valid with (1:=H3).
         ++ assumption.
         ++ apply perm_full_valid.
         ++ apply perm_full_mapped.
         ++ constructor.
            constructor.
            ** constructor.
            ** discriminate.
      -- rewrite <- Hmem_alloc.
         assumption.
      -- apply mem_stack_weaken_memenv with (Δ:='{m}).
         ++ assumption.
         ++ rewrite <- Hmem_alloc.
            rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
            ** apply mem_alloc_memenv_valid.
               --- apply cmap_valid_memenv_valid with (m0:=m).
                   apply mem_stack_valid with (1:=H3).
               --- rewrite <- cmap_dom_memenv_of in H2.
                   apply not_elem_of_dom with (1:=H2).
               --- constructor. constructor.
            ** assumption.
            ** constructor.
               constructor.
               --- constructor.
               --- discriminate.
         ++ rewrite <- Hmem_alloc.
            rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
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
    * inversion H8; subst.
      -- apply mem_stack_freed with (m1:=m'0).
         ++ assumption.
         ++ apply mem_stack_free with (1:=H18).
            ** rewrite mem_free_memenv_of.
               apply mem_free_forward.
            ** apply cmap_valid_subseteq with (m2:=mem_free o (m0 ∪ m'0)).
               --- assumption.
               --- rewrite mem_free_memenv_of.
                   apply mem_free_valid.
                   +++ assumption.
                   +++ apply mem_stack_valid with (1:=H8).
               --- assert (mem_freeable_perm o false m0). {
                     apply mem_freeable_perm_singleton with (1:=H16).
                   }
                   rewrite mem_free_union with (μ:=false).
                   +++ apply sep_union_subseteq_r.
                       apply sep_disjoint_list_double.
                       apply mem_free_disjoint with (2:=H6).
                       apply sep_disjoint_list_double.
                       assumption.
                   +++ apply sep_disjoint_list_double; assumption.
                   +++ assumption.
         ++ rewrite mem_free_union with (μ:=false).
            apply sep_union_subseteq_r.
            ** rewrite sep_disjoint_list_double.
               apply mem_free_disjoint with (μ:=false).
               --- rewrite <- sep_disjoint_list_double.
                   assumption.
               --- apply mem_freeable_perm_singleton with (1:=H16).
            ** rewrite sep_disjoint_list_double in H19; assumption.
            ** apply mem_freeable_perm_singleton with (1:=H16).
         ++ rewrite mem_free_memenv_of.
            apply mem_free_valid.
            ** assumption.
            ** assumption.
      -- 
         ++ 
            ** rewrite sep_disjoint_list_double in H19.
               destruct m0.
               destruct m'0.
               simpl in *.
               apply not_elem_of_dom.
               unfold disjoint in H19.
               unfold sep_disjoint in H19.
               unfold mem_sep_ops in H19.
               unfold cmap_ops in H19.
               pose proof (H19 o).
               apply mem_lookup_singleton in H16.
               --- simpl in H16.
                   unfold mem_lookup in H16.
                   unfold lookupE in H16.
                   unfold cmap_lookup in H16.
                   simpl in H16.
                   destruct (cmap_car0 !! o).
                   +++ destruct (cmap_car !! o).
                       *** 
               --- destruct 
               
            ** apply cmap_valid_weaken with (Γ1:=Γ) (Δ1:='{m}).
               --- assumption.
               --- apply mem_stack_valid with (1:=H3).
               --- reflexivity.
               --- apply insert_subseteq.
                   rewrite <- cmap_dom_memenv_of in H2.
                   apply not_elem_of_dom with (1:=H2).
               --- rewrite <- mem_alloc_memenv_of with (Γ0:=Γ) (Δ:=empty) (μ:=false) (γ:=perm_full) (v:=indetV sintT).
                   apply mem_alloc_valid' with (τ:=sintT%T).
                   +++ assumption.
                   +++ apply mem_stack_valid with (1:=H3).
                   +++ assumption.
                   +++ apply perm_full_valid.
                   +++ apply perm_full_mapped.
                   +++ constructor. constructor.
                       *** constructor.
                       *** discriminate.
                   +++ assumption.
                   +++ constructor. constructor.
                       *** constructor.
                       *** discriminate.
            ** assumption.
            ** apply val_new_typed.
               --- assumption.
               --- constructor.
                   constructor.
         ++ rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
            ** apply mem_alloc_index_typed.
            ** assumption.
            ** apply val_new_typed.
               --- assumption.
               --- constructor.
                   constructor.
         ++ rewrite mem_alloc_memenv_of with (Δ:=empty) (τ:=sintT%T).
            ** apply mem_alloc_index_alive.
            ** assumption.
            ** apply val_new_typed.
               --- assumption.
               --- constructor.
                   constructor.
         ++ assumption.
         ++ apply perm_full_valid.
         ++ apply perm_full_mapped.
         ++ constructor. constructor.
                       *** constructor.
                       *** discriminate.
         ++ Opaque mem_alloc.
            simpl in *.
            assert (mem_alloc Γ o false perm_full (indetV sintT) ∅ ∪ m = m2 ∪ m). {
              rewrite <- mem_alloc_union.
              - rewrite sep_left_id.
                + assumption.
                + eapply cmap_valid_sep_valid.
                  apply mem_stack_valid with (1:=H3).
              - assumption.
            }
            apply sep_cancel_r in H6.
            ** assert (val_new Γ sintT%BT = indetV sintT). {
                 rewrite val_new_base.
                 destruct (decide (sintT%BT = voidT%BT)); try discriminate.
                 reflexivity.
               }
               rewrite H8.
               rewrite H6.
               rewrite H8 in Hsingleton.
               apply Hsingleton.
            ** 

Admitted.

Theorem bigstep_sound `{Env K} s z:
  exec [] s (oreturn z) ->
  forall Γ δ S,
  Γ\ δ\ [] ⊢ₛ State [] (Stmt ↘ s) ∅ ⇒* S ->
  exists m,
  Γ\ δ\ [] ⊢ₛ S ⇒* State [] (Stmt (⇈ (intV{sintT} z)) s) m.
Admitted.
