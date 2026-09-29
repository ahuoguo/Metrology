module

public import Metrology.Coneris.WpTactics
public import Metrology.Coneris.DerivedLaws

/-!
# Proof mode for Coneris

Ported from clutch/theories/coneris/proofmode.v

Instantiates the generic `wp_*` tactics of `Metrology.Coneris.WpTactics` (Rocq:
`con_prob_lang/wp_tactics.v`) for the Coneris weakest precondition. The Rocq `gwp` is `wp` at
index type `()`; here it is iris-lean's `Wp.wp` (with the Coneris instance `pgl_wp'`) at index
type `Stuckness`, i.e. `Wp.wp (PROP := IProp GF) (Expr := expr)`, so that the tactics apply to
goals `WP e @ s; E {{ Φ }}`.

## Rocq → Lean mapping
* The instances keep the Rocq names: `rel_logic_wptactics_base`, `rel_logic_wptactics_bind`,
  `rel_logic_wptactics_pure`, `rel_logic_wptactics_heap`, `rel_logic_wptactics_tape`,
  `rel_logic_wptactics_atomic_concurrency`, `rel_logic_wptactics_frame_wand`, all with
  `laters = true`.
* The obligations are discharged by `pgl_wp_value'`, `pgl_wp_fupd`, `pgl_wp_bind`,
  `wp_pure_step_later`, `wp_alloc`, `wp_allocN`, `wp_load`, `wp_store`, `wp_alloc_tape`,
  `wp_rand_tape` (with the wand uncurried, Rocq: `bi.wand_curry`), `wp_cmpxchg_fail`,
  `wp_cmpxchg_suc`, `wp_xchg`, `wp_faa`, `pgl_wp_frame_wand`.
* As in Rocq, the tape points-to of the tactics ignores its fraction:
  `wptac_mapsto_tape l q N ns := l ↪N (N; ns)`.

## Added
* A test section (not in Rocq) with small programs verified with the tactics: pure reductions,
  `let`/`if`/pairs/projections/closures, allocation, load, store, `rand` (by `wp_apply`), tapes
  (`wp_alloctape`, `wp_randtape`), `fork`, `faa`, `xchg`, `cmpxchg`, `wp_bind`, `wp_rec` on a
  function hidden behind a definition, and `wp_smart_apply`.
-/

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris

section instances

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `rel_logic_wptactics_base`. -/
public instance rel_logic_wptactics_base :
    GwpTacticsBase GF Stuckness (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_wp_value _ _ _ _ := pgl_wp_value'
  wptac_wp_fupd _ _ _ _ := pgl_wp_fupd

/-- Rocq: `rel_logic_wptactics_bind`. -/
public instance rel_logic_wptactics_bind :
    GwpTacticsBind GF Stuckness (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_wp_bind K _ _ _ _ _ := pgl_wp_bind K

/-- Rocq: `rel_logic_wptactics_pure`. -/
public instance rel_logic_wptactics_pure :
    GwpTacticsPure GF Stuckness true (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_wp_pure_step _ _ _ _ _ _ _ _ hφ := wp_pure_step_later hφ

/-- Rocq: `rel_logic_wptactics_heap`. -/
public instance rel_logic_wptactics_heap :
    GwpTacticsHeap GF Stuckness true (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_mapsto l q v := l ↦{q} v
  wptac_mapsto_array l q vs := l ↦∗{q} vs
  wptac_wp_alloc E v a Φ := (wp_alloc (s := a) (E := E) v).trans (forall_elim Φ)
  wptac_wp_allocN E v n a Φ hn := (wp_allocN (s := a) (E := E) v n hn).trans (forall_elim Φ)
  wptac_wp_load E v l dq a Φ := (wp_load (s := a) (E := E) l dq v).trans (forall_elim Φ)
  wptac_wp_store E v v' l a Φ := (wp_store (s := a) (E := E) l v' v).trans (forall_elim Φ)

/-- Rocq: `rel_logic_wptactics_tape`. As in Rocq, the fraction of the tape points-to is
ignored. -/
public instance rel_logic_wptactics_tape :
    GwpTacticsTapes GF Stuckness true (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_mapsto_tape l _ N ns := l ↪N (N; ns)
  wptac_wp_alloctape E N z a Φ hN := (wp_alloc_tape (s := a) (E := E) N z hN).trans (forall_elim Φ)
  wptac_wp_rand_tape E N n z ns l _ a Φ hN := by
    iintro Hl HΦ
    iapply wp_rand_tape (s := a) (E := E) N l n ns z hN $$ Hl
    iintro !> ⟨Ht, %Hle⟩
    iapply HΦ $$ Ht
    ipureintro
    exact Hle

/-- Rocq: `rel_logic_wptactics_atomic_concurrency`. -/
public instance rel_logic_wptactics_atomic_concurrency :
    GwpTacticsAtomicConcurrency GF Stuckness true (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_mapsto_conc l q v := l ↦{q} v
  wptac_wp_cmpxchg_fail E Φ l dq v v1 v2 a hne hsafe :=
    (wp_cmpxchg_fail (s := a) (E := E) v v1 v2 l dq hsafe hne).trans (forall_elim Φ)
  wptac_wp_cmpxchg_suc E Φ l v v1 v2 a heq hsafe :=
    (wp_cmpxchg_suc (s := a) (E := E) v v1 v2 l hsafe heq).trans (forall_elim Φ)
  wptac_wp_xchg E Φ l v1 v2 a := (wp_xchg (s := a) (E := E) v1 v2 l).trans (forall_elim Φ)
  wptac_wp_faa E Φ l i1 i2 a := (wp_faa (s := a) (E := E) i1 i2 l).trans (forall_elim Φ)

/-- Rocq: `rel_logic_wptactics_frame_wand`. -/
public instance rel_logic_wptactics_frame_wand :
    GwpTacticsFrameWand GF Stuckness true (Wp.wp (PROP := IProp GF) (Expr := expr)) where
  wptac_wp_frame_wand _ _ _ _ _ := pgl_wp_frame_wand

end instances

section tests

variable {GF : BundledGFunctors} [conerisGS GF]

example : ⊢ WP (BinOp PlusOp (Val (LitV (LitInt 1))) (Val (LitV (LitInt 2)))) {{ v, (⌜v = LitV (LitInt 3)⌝ : IProp GF) }} := by
  wp_pures
  ipureintro
  rfl

example : ⊢ WP cpl(let x := #1 + #2; if x = #3 then (x, #true) else (#0, #false)) {{ v, (⌜v = PairV (LitV (LitInt 3)) (LitV (LitBool true))⌝ : IProp GF) }} := by
  wp_pures
  ipureintro
  rfl

example : ⊢ WP cpl(fst((#1, #2)) + snd((#3, #4))) {{ v, (⌜v = LitV (LitInt 5)⌝ : IProp GF) }} := by
  wp_pair
  wp_proj
  wp_pair
  wp_proj
  wp_op
  ipureintro
  rfl

example (Φ : val → IProp GF) : Φ (LitV (LitInt 2)) ⊢ WP cpl((λ x, x + #1) #1) {{ Φ }} := by
  iintro H
  wp_pures
  iexact H

example : ⊢ WP cpl(let l := ref(#1); l ← !l + #1; !l) {{ v, (⌜v = LitV (LitInt 2)⌝ : IProp GF) }} := by
  wp_alloc l as Hl
  wp_pures
  wp_load
  wp_pures
  wp_store
  wp_load
  ipureintro
  rfl

example : ⊢ WP cpl(let x := rand(#3); x + #0) {{ v, (⌜∃ n : ℕ, n ≤ 3 ∧ v = LitV (LitInt n)⌝ : IProp GF) }} := by
  wp_apply (wp_rand 3 3 rfl) with %n -
  · itrivial
  wp_pures
  ipureintro
  refine ⟨n, by omega, ?_⟩
  simp

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
    WP cpl(faa(#l, #2); cmpXchg(#l, #3, #5)) {{ v, ⌜v = PairV (LitV (LitInt 3)) (LitV (LitBool true))⌝ ∗ l ↦ LitV (LitInt 5) }} := by
  iintro Hl
  wp_faa
  wp_pures
  wp_cmpxchg_suc
  iframe Hl
  ipureintro
  rfl

example (l : Loc) : (l ↦{DFrac.discard} LitV (LitInt 1) : IProp GF) ⊢
    WP cpl(cmpXchg(#l, #3, #5)) {{ v, ⌜v = PairV (LitV (LitInt 1)) (LitV (LitBool false))⌝ }} := by
  iintro Hl
  wp_cmpxchg_fail
  ipureintro
  rfl

example (l : Loc) (z : ℤ) : (l ↦ LitV (LitInt z) : IProp GF) ⊢
    WP cpl(cmpXchg(#l, #0, #5)) {{ _v, True }} := by
  iintro Hl
  wp_cmpxchg as h1 | h2
  · itrivial
  · itrivial

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

variable {s : Stuckness} {E : CoPset}

/-- A closed function value, hidden behind a definition (Rocq: a `Definition` of a `val`). -/
def incr : val := cpl_val(λ l, l ← !l + #1)

/-- A spec for `incr`, in Texan-triple form. -/
theorem wp_incr (l : Loc) (z : ℤ) :
    {{ ▷ l ↦ LitV (LitInt z) }} (App (Val incr) (Val (LitV (LitLoc l)))) @ s; E
    {{ RET LitV LitUnit; l ↦ LitV (LitInt (z + 1)) }} := by
  iintro %Φ Hl HΦ
  wp_rec
  wp_load
  wp_pures
  wp_store
  iapply HΦ $$ Hl

example (l : Loc) : (l ↦ LitV (LitInt 0) : IProp GF) ⊢
    WP cpl(if #true then &incr #l else #()) {{ v, ⌜v = LitV LitUnit⌝ ∗ l ↦ LitV (LitInt (0 + 1)) }} := by
  iintro Hl
  wp_smart_apply wp_incr $$ Hl with Hl
  iframe Hl
  ipureintro
  rfl

example (l : Loc) : (l ↦ LitV (LitInt 0) : IProp GF) ⊢
    WP cpl((&incr #l; !#l) + #1) {{ v, ⌜v = LitV (LitInt 2)⌝ }} := by
  iintro Hl
  wp_bind (App _ _)
  wp_apply wp_incr $$ Hl with Hl
  wp_pures
  wp_load
  wp_pures
  ipureintro
  rfl

example (n : ℤ) : ⊢ WP cpl((λ x, x + #1) #n) {{ v, (⌜v = LitV (LitInt (n + 1))⌝ : IProp GF) }} := by
  wp_closure
  wp_lam
  wp_op
  ipureintro
  rfl

example (v : val) : ⊢ WP cpl(&v = #1) {{ w, (⌜w = LitV (LitBool (decide (v = LitV (LitInt 1))))⌝ : IProp GF) }} := by
  wp_pure
  ipureintro
  rfl

end tests

end Coneris
