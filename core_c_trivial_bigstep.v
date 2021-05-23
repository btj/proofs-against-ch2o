Require Export ZArith.
Require Export ch2o.core_c.expressions.

Notation store := (list (option Z)).

Inductive mem_stack `{Env K} (Γ : env K) (Δ : memenv K): stack K -> store -> mem K -> Prop :=
| mem_stack_empty m:
  mem_stack Γ Δ [] [] m
| mem_stack_alloc o mv m ρ st m':
  mem_singleton Γ Δ (addr_top o sintT%T) false full_perm
    (match mv with None => indetV sintT%T | Some z => intV{sintT} z end)
    sintT%T m ->
  mem_stack Γ Δ ρ st m' ->
  m ⊥ m' ->
  mem_stack Γ Δ ((o, sintT%T)::ρ) (mv::st) (m ∪ m')
.

Inductive eval: store -> expr -> Z -> Prop :=
| eval_lit st z:
  eval st (# intV{sintT} z) z
| eval_var st i z:
  st !! i = Some (Some z) ->
  eval st (load (var i)) z
.

Lemma eval_sound:
  eval st e z ->
  mem_stack ρ st m ->
  ⟦ e ⟧ Γ ρ m = Some (# intV{sintT} z).
  
Inductive outcome := onormal(s: store) | oreturn(z: Z).

Inductive exec: store -> stmt -> outcome -> Prop :=
| exec_local st s:
  exec (None::st) s O ->
  exec st (local{sintT%BT} s) O
| exec_assign st i e z:
  eval st e z ->
  exec st (var i ::= cast{sintT%BT} e) (onormal (<i:=Some z>st))
| exec_seq st s1 st' s2 O:
  exec st s1 (onormal st') ->
  exec st s2 O ->
  exec st (s1 ;; s2) O
| exec_ret st e:
  eval st e z ->
  exec st (ret (cast{sintT%BT} e)) (oreturn z)
.

Definition is_final_state S := forall Γ δ S', ~ Γ\ δ\ [] ⊢ₛ S ⇒ S'.

Lemma bigstep_sound_lemma st s O (P: Prop):
  exec st s O ->
  forall Γ δ k m S,
  is_final_state S ->
  Γ\ δ\ [] ⊢ₛ State k (Stmt ↘ s) m ⇒* S ->
  mem_stack (rlocals [] k) st m ->
  (forall st' m',
   O = onormal st' ->
   mem_stack (rlocals [] k) st' m' ->
   Γ\ δ\ [] ⊢ₛ State k (Stmt ↗ s) m' ⇒* S ->
   P) ->
  (forall z st' m',
   O = oret z ->
   mem_stack (rlocals [] k) st' m' ->
   Γ\ δ\ [] ⊢ₛ State k (Stmt (⇈ intV{sintT} z) s) m' ⇒* S ->
   P) ->
  P.

Theorem bigstep_sound s z:
  exec [] s (oreturn z) ->
  forall Γ δ S,
  Γ\ δ\ [] ⊢ₛ State [] (Stmt ↘ s) ∅ ⇒* S ->
  exists m,
  Γ\ δ\ [] ⊢ₛ S ⇒* State [] (Stmt ⇈ (intV{sintT} z) s) m.
