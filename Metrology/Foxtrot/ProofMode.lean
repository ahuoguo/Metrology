module

public import Metrology.Coneris.WpTactics
public import Metrology.Foxtrot.DerivedLaws

/-!
# Proof mode for Foxtrot

Ported from clutch/theories/foxtrot/proofmode.v

Instantiates the generic `wp_*` tactics of `Metrology.Coneris.WpTactics` (Rocq:
`con_prob_lang/wp_tactics.v`) for the Foxtrot weakest precondition (left-hand side), as
`Metrology/Coneris/ProofMode.lean` does for Coneris. The Rocq `gwp` is `wp` at index type `()`;
here it is iris-lean's `Wp.wp` (with the Foxtrot instance `Foxtrot.wp'`) at index type
`Stuckness`, i.e. `Wp.wp (PROP := IProp GF) (Expr := expr)`, so that the tactics apply to
goals `WP e @ s; E {{ Φ }}`.

## Rocq → Lean mapping
* LHS instances keep the Rocq names: `rel_logic_wptactics_base`, `rel_logic_wptactics_bind`,
  `rel_logic_wptactics_pure`, `rel_logic_wptactics_frame_wand`, `rel_logic_wptactics_heap`,
  `rel_logic_wptactics_tape`, `rel_logic_wptactics_atomic_concurrency`, all with
  `laters = true`. Their obligations are discharged by `wp_value'`, `wp_fupd`, `wp_bind`,
  `wp_pure_step_later`, `wp_frame_wand`, `wp_alloc`, `wp_allocN`, `wp_load`, `wp_store`,
  `wp_alloc_tape`, `wp_rand_tape` (with the wand uncurried, Rocq: `bi.wand_curry`),
  `wp_cmpxchg_fail`, `wp_cmpxchg_suc`, `wp_xchg`, `wp_faa`.
* As in Rocq, the tape points-to of the tactics ignores its fraction:
  `wptac_mapsto_tape l q N ns := l ↪N (N; ns)`.
* The classes live in namespace `Coneris` (where `WpTactics.lean` declares them); they are
  referred to by their qualified names, `Coneris.GwpTacticsBase` etc.

## Deviations / omissions
* RHS instances `rel_logic_tptactics_pure` (`UpdPure pupd`), `rel_logic_tptactics_heap`
  (`UpdHeap pupd`), `rel_logic_tptactics_concurrency` (`UpdAtomicConcurrency pupd`) and
  `rel_logic_tptactics_tapes` (`UpdTapes pupd`) live in `Metrology.Foxtrot.SpecProofMode`,
  which imports the port of `con_prob_lang/spec/spec_tactics.v`
  (`Metrology.ConProbLang.Spec.SpecTactics`, the classes and the `tp_*` tactics). This file
  states and proves each obligation (the field of the Rocq class, with `upd := pupd`) as a
  theorem named `rel_logic_tptactics_<field>`, e.g. `rel_logic_tptactics_upd_pure_step`
  (Rocq field `tptac_upd_pure_step`); `SpecProofMode` builds the instances from them.
* The Rocq test `test_wp_tp_pures` uses `tp_pures j`; here (before the `tp_*` tactics are
  available) the RHS pure steps are taken with `pupd_step_pure` (the lemma behind `tp_pure`),
  eliminated in the WP goal by `imod`. A version with `tp_pures j` is in
  `Metrology.Foxtrot.SpecProofMode`.

## Added
* A test section (not in Rocq, besides `test_wp_tp_pures`) with small programs verified with
  the LHS tactics: `wp_pures`, `wp_alloc`, `wp_load`, `wp_store`, `wp_apply` with `wp_rand`,
  tapes, `fork`, `faa`, `cmpxchg`, `xchg`.
-/

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

section instances

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `rel_logic_wptactics_base`. -/
public instance rel_logic_wptactics_base :
    Coneris.GwpTacticsBase GF Stuckness (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_wp_value _ _ _ _ := wp_value'
  wptac_wp_fupd _ _ _ _ := wp_fupd

/-- Rocq: `rel_logic_wptactics_bind`. -/
public instance rel_logic_wptactics_bind :
    Coneris.GwpTacticsBind GF Stuckness (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_wp_bind K _ _ _ _ _ := wp_bind K

/-- Rocq: `rel_logic_wptactics_pure`. -/
public instance rel_logic_wptactics_pure :
    Coneris.GwpTacticsPure GF Stuckness true (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_wp_pure_step _ _ _ _ _ _ _ _ hφ := wp_pure_step_later hφ

/-- Rocq: `rel_logic_wptactics_frame_wand`. -/
public instance rel_logic_wptactics_frame_wand :
    Coneris.GwpTacticsFrameWand GF Stuckness true (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_wp_frame_wand _ _ _ _ _ := wp_frame_wand

/-- Rocq: `rel_logic_wptactics_heap`. -/
public instance rel_logic_wptactics_heap :
    Coneris.GwpTacticsHeap GF Stuckness true (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_mapsto l q v := l ↦{q} v
  wptac_mapsto_array l q vs := l ↦∗{q} vs
  wptac_wp_alloc E v a Φ := (wp_alloc (s := a) (E := E) v).trans (forall_elim Φ)
  wptac_wp_allocN E v n a Φ hn := (wp_allocN (s := a) (E := E) v n hn).trans (forall_elim Φ)
  wptac_wp_load E v l dq a Φ := (wp_load (s := a) (E := E) l dq v).trans (forall_elim Φ)
  wptac_wp_store E v v' l a Φ := (wp_store (s := a) (E := E) l v' v).trans (forall_elim Φ)

/-- Rocq: `rel_logic_wptactics_tape`. As in Rocq, the fraction of the tape points-to is
ignored. -/
public instance rel_logic_wptactics_tape :
    Coneris.GwpTacticsTapes GF Stuckness true (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_mapsto_tape l _ N ns := l ↪N (N; ns)
  wptac_wp_alloctape E N z a Φ hN :=
    (wp_alloc_tape (s := a) (E := E) N z hN).trans (forall_elim Φ)
  wptac_wp_rand_tape E N n z ns l _ a Φ hN := by
    iintro Hl HΦ
    iapply wp_rand_tape (s := a) (E := E) N l n ns z hN $$ Hl
    iintro !> ⟨Ht, %Hle⟩
    iapply HΦ $$ Ht
    ipureintro
    exact Hle

/-- Rocq: `rel_logic_wptactics_atomic_concurrency`. -/
public instance rel_logic_wptactics_atomic_concurrency :
    Coneris.GwpTacticsAtomicConcurrency GF Stuckness true
      (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_mapsto_conc l q v := l ↦{q} v
  wptac_wp_cmpxchg_fail E Φ l dq v v1 v2 a hne hsafe :=
    (wp_cmpxchg_fail (s := a) (E := E) v v1 v2 l dq hsafe hne).trans (forall_elim Φ)
  wptac_wp_cmpxchg_suc E Φ l v v1 v2 a heq hsafe :=
    (wp_cmpxchg_suc (s := a) (E := E) v v1 v2 l hsafe heq).trans (forall_elim Φ)
  wptac_wp_xchg E Φ l v1 v2 a := (wp_xchg (s := a) (E := E) v1 v2 l).trans (forall_elim Φ)
  wptac_wp_faa E Φ l i1 i2 a := (wp_faa (s := a) (E := E) i1 i2 l).trans (forall_elim Φ)

end instances

/-! ## RHS (Rocq: the `Upd*` instances of `spec_tactics.v`, as theorems) -/

@[expose] public section

section rhs

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `rel_logic_tptactics_pure` (field `tptac_upd_pure_step` of `UpdPure pupd`). -/
theorem rel_logic_tptactics_upd_pure_step (j : ℕ) (E : CoPset) (e1 e2 : expr) (φ : Prop)
    (n : ℕ) (H : PureExec (Λ := con_prob_lang) φ n e1 e2) (Hφ : φ) :
    j ⤇ e1 ⊢@{IProp GF} pupd E E (j ⤇ e2) :=
  pupd_step_pure (H2 := H) φ n e1 e2 j [] E Hφ

/-- Rocq: `rel_logic_tptactics_heap` (field `tptac_upd_alloc` of `UpdHeap pupd`). -/
theorem rel_logic_tptactics_upd_alloc (j : ℕ) (K : List ectx_item) (E : CoPset) (v : val) :
    j ⤇ fill K (Alloc (Val v)) ⊢@{IProp GF}
      pupd E E iprop(∃ l, l ↦ₛ v ∗ j ⤇ fill K (Val (LitV (LitLoc l)))) := by
  iintro Hj
  imod pupd_alloc E K (Val v) v j $$ Hj with ⟨%l, Hj, Hl⟩
  imodintro
  iexists l
  iframe

/-- Rocq: `rel_logic_tptactics_heap` (field `tptac_upd_load` of `UpdHeap pupd`). -/
theorem rel_logic_tptactics_upd_load (j : ℕ) (K : List ectx_item) (E : CoPset) (v : val)
    (l : Loc) (dq : DFrac) :
    l ↦ₛ{dq} v ⊢@{IProp GF} j ⤇ fill K (Load (Val (LitV (LitLoc l)))) -∗
      pupd E E iprop(l ↦ₛ{dq} v ∗ j ⤇ fill K (Val v)) := by
  iintro Hl Hj
  imod pupd_load E K l dq v j $$ [Hj Hl] with ⟨Hj, Hl⟩
  · iframe
  imodintro
  iframe

/-- Rocq: `rel_logic_tptactics_heap` (field `tptac_upd_store` of `UpdHeap pupd`). -/
theorem rel_logic_tptactics_upd_store (j : ℕ) (K : List ectx_item) (E : CoPset) (v v' : val)
    (l : Loc) :
    l ↦ₛ v' ⊢@{IProp GF} j ⤇ fill K (Store (Val (LitV (LitLoc l))) (Val v)) -∗
      pupd E E iprop(l ↦ₛ v ∗ j ⤇ fill K (Val (LitV LitUnit))) := by
  iintro Hl Hj
  imod pupd_store E K l v' (Val v) v j $$ [Hj Hl] with ⟨Hj, Hl⟩
  · iframe
  imodintro
  iframe

/-- Rocq: `rel_logic_tptactics_concurrency` (field `tptac_upd_cmpxchg_fail` of
`UpdAtomicConcurrency pupd`). -/
theorem rel_logic_tptactics_upd_cmpxchg_fail (j : ℕ) (K : List ectx_item) (E : CoPset) (l : Loc)
    (dq : DFrac) (v v1 v2 : val) (Hne : v ≠ v1) (Hsafe : vals_compare_safe v v1) :
    l ↦ₛ{dq} v ⊢@{IProp GF} j ⤇ fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) -∗
      pupd E E iprop(l ↦ₛ{dq} v ∗ j ⤇ fill K (Val (PairV v (LitV (LitBool false))))) := by
  iintro Hl Hj
  imod pupd_cmpxchg_fail E K l dq v v1 v2 j Hsafe Hne $$ [Hj Hl] with ⟨Hj, Hl⟩
  · iframe
  imodintro
  iframe

/-- Rocq: `rel_logic_tptactics_concurrency` (field `tptac_upd_cmpxchg_suc` of
`UpdAtomicConcurrency pupd`). -/
theorem rel_logic_tptactics_upd_cmpxchg_suc (j : ℕ) (K : List ectx_item) (E : CoPset) (l : Loc)
    (v v1 v2 : val) (Heq : v = v1) (Hsafe : vals_compare_safe v v1) :
    l ↦ₛ v ⊢@{IProp GF} j ⤇ fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) -∗
      pupd E E iprop(l ↦ₛ v2 ∗ j ⤇ fill K (Val (PairV v (LitV (LitBool true))))) := by
  iintro Hl Hj
  imod pupd_cmpxchg_suc E K l v v1 v2 j Hsafe Heq $$ [Hj Hl] with ⟨Hj, Hl⟩
  · iframe
  imodintro
  iframe

/-- Rocq: `rel_logic_tptactics_concurrency` (field `tptac_upd_xchg` of
`UpdAtomicConcurrency pupd`). -/
theorem rel_logic_tptactics_upd_xchg (j : ℕ) (K : List ectx_item) (E : CoPset) (l : Loc)
    (v1 v2 : val) :
    l ↦ₛ v1 ⊢@{IProp GF} j ⤇ fill K (Xchg (Val (LitV (LitLoc l))) (Val v2)) -∗
      pupd E E iprop(l ↦ₛ v2 ∗ j ⤇ fill K (Val v1)) := by
  iintro Hl Hj
  imod pupd_xchg E K l v1 v2 j $$ [Hj Hl] with ⟨Hj, Hl⟩
  · iframe
  imodintro
  iframe

/-- Rocq: `rel_logic_tptactics_concurrency` (field `tptac_upd_faa` of
`UpdAtomicConcurrency pupd`). -/
theorem rel_logic_tptactics_upd_faa (j : ℕ) (K : List ectx_item) (E : CoPset) (l : Loc)
    (i1 i2 : ℤ) :
    l ↦ₛ LitV (LitInt i1) ⊢@{IProp GF}
      j ⤇ fill K (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt i2)))) -∗
      pupd E E iprop(l ↦ₛ LitV (LitInt (i1 + i2)) ∗ j ⤇ fill K (Val (LitV (LitInt i1)))) := by
  iintro Hl Hj
  imod pupd_faa E K l i1 i2 j $$ [Hj Hl] with ⟨Hj, Hl⟩
  · iframe
  imodintro
  iframe

/-- Rocq: `rel_logic_tptactics_concurrency` (field `tptac_upd_fork` of
`UpdAtomicConcurrency pupd`). -/
theorem rel_logic_tptactics_upd_fork (j : ℕ) (K : List ectx_item) (E : CoPset) (e : expr) :
    j ⤇ fill K (Fork e) ⊢@{IProp GF}
      pupd E E iprop(∃ k, k ⤇ e ∗ j ⤇ fill K (Val (LitV LitUnit))) := by
  iintro Hj
  imod pupd_fork E K e j $$ Hj with ⟨Hj, %k, Hk⟩
  imodintro
  iexists k
  iframe

/-- Rocq: `rel_logic_tptactics_tapes` (field `tptac_upd_alloctape` of `UpdTapes pupd`). -/
theorem rel_logic_tptactics_upd_alloctape (j : ℕ) (K : List ectx_item) (E : CoPset) (N : ℕ)
    (z : ℤ) (hN : N = z.toNat) :
    True ⊢@{IProp GF} j ⤇ fill K (AllocTape (Val (LitV (LitInt z)))) -∗
      pupd E E iprop(∃ l, l ↪ₛN (N; []) ∗ j ⤇ fill K (Val (LitV (LitLbl l)))) := by
  iintro - Hj
  iapply pupd_alloc_tape E K j z N hN $$ Hj

end rhs

end

/-! ## Tests -/

section foxtrot_test

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness}

/-- Rocq: `test_wp_tp_pures`. The RHS steps (Rocq: `tp_pures j`) are taken with
`pupd_step_pure`. -/
theorem test_wp_tp_pures (j : ℕ) (E : CoPset) (K : List ectx_item) :
    {{ j ⤇ fill K (BinOp PlusOp (BinOp PlusOp (Val (LitV (LitInt 2))) (Val (LitV (LitInt 2))))
        (Val (LitV (LitInt 2)))) }}
      (BinOp PlusOp (Val (LitV (LitInt 3))) (Val (LitV (LitInt 3)))) @ s; E
    {{ RET LitV (LitInt 6); (j ⤇ fill K (Val (LitV (LitInt 6))) : IProp GF) }} := by
  have h1 : j ⤇ fill K (BinOp PlusOp (BinOp PlusOp (Val (LitV (LitInt 2)))
      (Val (LitV (LitInt 2)))) (Val (LitV (LitInt 2)))) ⊢@{IProp GF}
      pupd E E (j ⤇ fill K (BinOp PlusOp (Val (LitV (LitInt 4))) (Val (LitV (LitInt 2))))) :=
    pupd_step_pure (H2 := pure_binop PlusOp (LitV (LitInt 2)) (LitV (LitInt 2))
      (LitV (LitInt 4))) _ 1 _ _ j (BinOpLCtx PlusOp (LitV (LitInt 2)) :: K) E rfl
  have h2 := pupd_step_pure (GF := GF) (H2 := pure_binop PlusOp (LitV (LitInt 4))
    (LitV (LitInt 2)) (LitV (LitInt 6))) _ 1 _ _ j K E rfl
  iintro %Ψ Hs HΨ
  imod h1 $$ Hs with Hs
  imod h2 $$ Hs with Hs
  wp_pures
  iapply HΨ $$ Hs

example : ⊢ WP (BinOp PlusOp (Val (LitV (LitInt 1))) (Val (LitV (LitInt 2))))
    {{ v, (⌜v = LitV (LitInt 3)⌝ : IProp GF) }} := by
  wp_pures
  ipureintro
  rfl

example : ⊢ WP cpl(let x := #1 + #2; if x = #3 then (x, #true) else (#0, #false))
    {{ v, (⌜v = PairV (LitV (LitInt 3)) (LitV (LitBool true))⌝ : IProp GF) }} := by
  wp_pures
  ipureintro
  rfl

example : ⊢ WP cpl(let l := ref(#1); l ← !l + #1; !l)
    {{ v, (⌜v = LitV (LitInt 2)⌝ : IProp GF) }} := by
  wp_alloc l as Hl
  wp_pures
  wp_load
  wp_pures
  wp_store
  wp_load
  ipureintro
  rfl

example : ⊢ WP cpl(let x := rand(#3); x + #0)
    {{ v, (⌜∃ n : ℕ, n ≤ 3 ∧ v = LitV (LitInt n)⌝ : IProp GF) }} := by
  wp_apply (wp_rand 3 3 rfl) with %n %Hn
  · itrivial
  wp_pures
  ipureintro
  exact ⟨n, Hn, by simp⟩

example : ⊢ WP cpl(let α := alloc(#1); rand(α) #1) {{ _v, (True : IProp GF) }} := by
  wp_alloctape α as Hα
  wp_pures
  wp_apply (wp_rand_tape_empty 1 1 α rfl) $$ Hα with %n Hα
  itrivial

example (α : Loc) : (α ↪N (3; [2]) : IProp GF) ⊢
    WP cpl(rand(#lbl(α)) #3) {{ v, ⌜v = LitV (LitInt 2)⌝ ∗ α ↪N (3; []) }} := by
  iintro Hα
  wp_randtape as %Hle
  iframe Hα
  ipureintro
  rfl

example (l : Loc) : (l ↦ LitV (LitInt 1) : IProp GF) ⊢
    WP cpl(faa(#l, #2); cmpXchg(#l, #3, #5))
      {{ v, ⌜v = PairV (LitV (LitInt 3)) (LitV (LitBool true))⌝ ∗ l ↦ LitV (LitInt 5) }} := by
  iintro Hl
  wp_faa
  wp_pures
  wp_cmpxchg_suc
  iframe Hl
  ipureintro
  rfl

example (l : Loc) : (l ↦ LitV (LitInt 1) : IProp GF) ⊢
    WP cpl(xchg(#l, #2); !#l) {{ v, ⌜v = LitV (LitInt 2)⌝ }} := by
  iintro Hl
  wp_xchg
  wp_load
  ipureintro
  rfl

example : ⊢ WP cpl(allocn(#2, #0)) {{ _v, (True : IProp GF) }} := by
  wp_alloc l as Hl
  itrivial

example (Φ : val → IProp GF) : ▷ Φ (LitV LitUnit) ⊢ WP cpl(fork(#1 + #1)) {{ Φ }} := by
  iintro HΦ
  wp_apply wp_fork $$ [] HΦ
  wp_pures
  itrivial

end foxtrot_test

end Foxtrot
