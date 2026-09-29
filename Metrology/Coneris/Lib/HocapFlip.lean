module

public import Metrology.Coneris.Lib.Flip
public import Metrology.Coneris.Lib.HocapRand

/-!
# Hocap flip specs

Ported from clutch/theories/coneris/lib/hocap_flip.v

An abstract spec for a flip module that allows presampling tapes.

## Rocq → Lean mapping
* `Class flip_spec `{!conerisGS Σ} := FlipSpec {...}` is the Lean `class flip_spec GF` (over
  `[conerisGS GF]`) with the same field names: `flip_allocate_tape`, `flip_tape`, `flipG`,
  `flip_tapes`, `flip_tapes_timeless`, `flip_tapes_exclusive`, `flip_tapes_presample`,
  `flip_allocate_tape_spec`, `flip_tape_spec_some`. As in `Coneris.Lib.HocapRand`:
  - the implicit `{L : flipG Σ}` is an explicit argument `(L : flipG GF)`;
  - the `#[global] flip_tapes_timeless ::` instance field is re-exported as the global instance
    `flip_spec_flip_tapes_timeless`;
  - errors are `ℝ≥0∞`: the hypothesis `∀ x, 0 <= ε2 x` of `flip_tapes_presample` is dropped,
    `(ε2 true + ε2 false)/2 <= ε` is kept literally (`ℝ≥0∞` division by `2 ≠ 0`);
  - `P -∗ Q -∗ R` fields are stated as `⊢ P -∗ Q -∗ R`; Texan triples are iris-lean's
    `{{ P }} e @ E {{ x, RET v; Q }}`; `RET #n` (`n : bool`) is `RET LitV (LitBool n)`.
* Section `instantiate_flip`: `flip_spec1` (Rocq: `#[local] Program Definition`) is a definition
  (not an instance) over `[r1 : rand_spec GF]`. The programs are transcribed with the `cpl`
  notation; `#1%nat` is `#1`. `fmap (FMap:=list_fmap) bool_to_nat ns` is
  `ns.map bool_to_nat`. The `Next Obligation`s are the helper theorems `flip_spec1_*`.
  `bool_to_nat`, `nat_to_bool` are the helpers of `Coneris.Lib.Flip`.
* Section `test`: `flip_presample_spec_simple`, for `[F : flip_spec GF]` and `(L : F.flipG GF)`.

## Omitted
* The commented-out Rocq code (`is_flip` in `flip_tapes_presample` and in the test).

## Added
* `flip_tapes1` (the `flip_tapes` field of `flip_spec1`), its `Timeless` instance, and the
  helper `nat_to_bool_bool_to_nat_fin` (Rocq: `repeat (inv_fin n; ...)`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris.Lib.Conversion Coneris.Lib.Flip Coneris.Lib.HocapRand

namespace Coneris.Lib.HocapFlip

/-- Rocq: `flip_spec`. -/
class flip_spec (GF : BundledGFunctors) [conerisGS GF] where
  -- * Operations
  flip_allocate_tape : val
  flip_tape : val
  -- * Ghost state
  /-- The assumptions about `Σ`. -/
  flipG : BundledGFunctors → Type
  -- * Predicates
  flip_tapes (L : flipG GF) (α : val) (ns : List Bool) : IProp GF
  -- * General properties of the predicates
  flip_tapes_timeless (L : flipG GF) (α : val) (ns : List Bool) : Timeless (flip_tapes L α ns)
  flip_tapes_exclusive (L : flipG GF) (α : val) (ns ns' : List Bool) :
    ⊢ flip_tapes L α ns -∗ flip_tapes L α ns' -∗ False
  flip_tapes_presample (L : flipG GF) (E : CoPset) (α : val) (ns : List Bool) (ε : ℝ≥0∞)
    (ε2 : Bool → ℝ≥0∞) (Hineq : (ε2 true + ε2 false) / 2 ≤ ε) :
    ⊢ flip_tapes L α ns -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Bool, ↯ (ε2 n) ∗ flip_tapes L α (ns ++ [n]))
  -- * Program specs
  flip_allocate_tape_spec (L : flipG GF) (E : CoPset) :
    {{ True }} cpl(v(&flip_allocate_tape) #()) @ E {{ v, RET v; flip_tapes L v [] }}
  flip_tape_spec_some (L : flipG GF) (E : CoPset) (α : val) (n : Bool) (ns : List Bool) :
    {{ flip_tapes L α (n :: ns) }} cpl(v(&flip_tape) v(&α)) @ E
    {{ RET LitV (LitBool n); flip_tapes L α ns }}

/-- Rocq: `#[global] flip_tapes_timeless` (the instance). -/
instance flip_spec_flip_tapes_timeless {GF : BundledGFunctors} [conerisGS GF] [F : flip_spec GF]
    (L : F.flipG GF) (α : val) (ns : List Bool) : Timeless (F.flip_tapes L α ns) :=
  F.flip_tapes_timeless L α ns

/-! ## Instantiate flip -/

section instantiate_flip

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF]

/-- Rocq: `flip_allocate_tape` of `flip_spec1`. -/
def flip_allocate_tape1 : val := cpl_val(λ <>, v(&r1.rand_allocate_tape) #1)

/-- Rocq: `flip_tape` of `flip_spec1`. -/
def flip_tape1 : val := cpl_val(λ α, &int_to_bool (v(&r1.rand_tape) α #1))

/-- Rocq: `flip_tapes` of `flip_spec1`. -/
def flip_tapes1 (L : r1.randG GF) (α : val) (ns : List Bool) : IProp GF :=
  r1.rand_tapes L α (1, ns.map bool_to_nat)

instance flip_tapes1_timeless (L : r1.randG GF) (α : val) (ns : List Bool) :
    Timeless (flip_tapes1 L α ns) := by
  unfold flip_tapes1; infer_instance

/-- Helper: `bool_to_nat (nat_to_bool n) = n` for `n : fin 2`. -/
theorem nat_to_bool_bool_to_nat_fin (n : Fin 2) : bool_to_nat (nat_to_bool (n : ℕ)) = (n : ℕ) := by
  fin_cases n <;> rfl

/-- Rocq: first `Next Obligation` of `flip_spec1`. -/
theorem flip_spec1_flip_tapes_exclusive (L : r1.randG GF) (α : val) (ns ns' : List Bool) :
    ⊢ flip_tapes1 L α ns -∗ flip_tapes1 L α ns' -∗ False := by
  unfold flip_tapes1
  iintro H1 H2
  iapply r1.rand_tapes_exclusive $$ H1 H2

/-- Rocq: second `Next Obligation` of `flip_spec1`. -/
theorem flip_spec1_flip_tapes_presample (L : r1.randG GF) (E : CoPset) (α : val)
    (ns : List Bool) (ε : ℝ≥0∞) (ε2 : Bool → ℝ≥0∞) (Hineq : (ε2 true + ε2 false) / 2 ≤ ε) :
    ⊢ flip_tapes1 L α ns -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Bool, ↯ (ε2 n) ∗ flip_tapes1 L α (ns ++ [n])) := by
  unfold flip_tapes1
  iintro Hfrag Hε
  imod r1.rand_tapes_presample L E α 1 (ns.map bool_to_nat) ε
    (fun x => ε2 (nat_to_bool (x : ℕ)))
    (by rw [flip_SeriesC_unif, one_div, ← ENNReal.div_eq_inv_mul]; exact Hineq)
    $$ Hfrag Hε with ⟨%n, Hε, Hfrag⟩
  imodintro
  iexists nat_to_bool (n : ℕ)
  iframe Hε
  rw [List.map_append, List.map_singleton, nat_to_bool_bool_to_nat_fin]
  iexact Hfrag

/-- Rocq: third `Next Obligation` of `flip_spec1`. -/
theorem flip_spec1_flip_allocate_tape_spec (L : r1.randG GF) (E : CoPset) :
    {{ True }} cpl(v(&flip_allocate_tape1) #()) @ E
    {{ v, RET v; flip_tapes1 L v [] }} := by
  iintro %Φ - HΦ
  unfold flip_allocate_tape1
  wp_pures
  wp_apply r1.rand_allocate_tape_spec L E 1 $$ [] with %v Hv
  · itrivial
  iapply HΦ
  unfold flip_tapes1
  simp only [List.map_nil]
  iexact Hv

/-- Rocq: fourth `Next Obligation` of `flip_spec1`. -/
theorem flip_spec1_flip_tape_spec_some (L : r1.randG GF) (E : CoPset) (α : val) (n : Bool)
    (ns : List Bool) :
    {{ flip_tapes1 L α (n :: ns) }} cpl(v(&flip_tape1) v(&α)) @ E
    {{ RET LitV (LitBool n); flip_tapes1 L α ns }} := by
  unfold flip_tapes1
  iintro %Φ Hfrag HΦ
  unfold flip_tape1
  wp_pures
  simp only [List.map_cons]
  wp_apply r1.rand_tape_spec_some L E α 1 (bool_to_nat n) (ns.map bool_to_nat) $$ Hfrag
    with Hfrag
  wp_apply wp_int_to_bool $$ [] with -
  · itrivial
  have hn : Z_to_bool ((bool_to_nat n : ℕ) : ℤ) = n := by cases n <;> rfl
  rw [hn]
  iapply HΦ $$ Hfrag

/-- Rocq: `flip_spec1` (a `#[local] Program Definition`). -/
@[instance_reducible]
def flip_spec1 : flip_spec GF where
  flip_allocate_tape := flip_allocate_tape1
  flip_tape := flip_tape1
  flipG := r1.randG
  flip_tapes L α ns := flip_tapes1 L α ns
  flip_tapes_timeless L α ns := flip_tapes1_timeless L α ns
  flip_tapes_exclusive L := flip_spec1_flip_tapes_exclusive L
  flip_tapes_presample L := flip_spec1_flip_tapes_presample L
  flip_allocate_tape_spec L := flip_spec1_flip_allocate_tape_spec L
  flip_tape_spec_some L := flip_spec1_flip_tape_spec_some L

end instantiate_flip

/-! ## Test -/

section test

variable {GF : BundledGFunctors} [conerisGS GF] [F : flip_spec GF]

/-- Rocq: `flip_presample_spec_simple`. -/
theorem flip_presample_spec_simple (L : F.flipG GF) (E : CoPset) (α : val) (ns : List Bool)
    (ε : ℝ≥0∞) (ε2 : Bool → ℝ≥0∞) (Hineq : (ε2 true + ε2 false) / 2 ≤ ε) :
    ⊢ F.flip_tapes L α ns -∗ ↯ ε -∗
      wp_update E iprop(∃ b : Bool, F.flip_tapes L α (ns ++ [b]) ∗ ↯ (ε2 b)) := by
  iintro Hfrag Herr
  iapply wp_update_state_update
  imod F.flip_tapes_presample L E α ns ε ε2 Hineq $$ Hfrag Herr with ⟨%b, Herr, Hfrag⟩
  imodintro
  iexists b
  iframe

end test

end Coneris.Lib.HocapFlip
