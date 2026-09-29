module

public import Metrology.Coneris.ErrorRules

/-!
# Hocap rand specs

Ported from clutch/theories/coneris/lib/hocap_rand.v

An abstract spec for a rand module that allows presampling tapes.

## Rocq → Lean mapping
* `Class rand_spec `{!conerisGS Σ} := RandSpec {...}` is the Lean `class rand_spec GF` (over
  `[conerisGS GF]`) with the same field names: `rand_allocate_tape`, `rand_tape`, `randG`,
  `rand_tapes`, `rand_tapes_timeless`, `rand_tapes_exclusive`, `rand_tapes_valid`,
  `rand_tapes_presample`, `rand_allocate_tape_spec`, `rand_tape_spec_some`.
  - As in `Coneris.Lib.Lock`, the implicit `{L : randG Σ}` (Rocq finds it by type class search)
    is an explicit argument `(L : randG GF)`.
  - The `#[global] rand_tapes_timeless ::` instance field is a field, re-exported as the global
    instance `rand_spec_rand_tapes_timeless`.
  - Errors are `ℝ≥0∞`: the hypothesis `∀ x, 0 <= ε2 x` of `rand_tapes_presample` is dropped;
    `SeriesC (λ n, 1 / (S tb) * ε2 n) <= ε` is `∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε`.
  - `Forall (λ n, n <= tb) ns` is `∀ n ∈ ns, n ≤ tb`; `fin_to_nat n` is `(n : ℕ)`.
  - `P -∗ Q -∗ R` fields are stated as `⊢ P -∗ Q -∗ R`.
  - Texan triples `{{{ P }}} e @ E {{{ x, RET v; Q }}}` are iris-lean's
    `{{ P }} e @ E {{ x, RET v; Q }}`. `#tb` (`tb : nat`) is `#tb` in the `cpl` notation
    (`LitV (LitInt tb)`); `RET #n` is `RET LitV (LitInt n)`.
* Section `impl`: `randG1` is an empty class; `rand_spec1` (Rocq: `#[local] Program Definition`)
  is a definition (not an instance). The programs are transcribed with the `cpl` notation.
  The `Next Obligation`s are the helper theorems `rand_spec1_*`.
* Section `checks`: `wp_rand_tape_1`, `wp_presample_adv_comp_rand_tape` (same names), for an
  arbitrary `[r1 : rand_spec GF]` and `(L : r1.randG GF)`.

## Omitted
* `Local Opaque INR`, `Local Opaque enum_uniform_fin_list`: Rocq-specific simplification
  settings.
* The commented-out Rocq code (`flipG1_tapes`, `rand_inv_pred1`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.HocapRand

/-- Rocq: `rand_spec`. -/
class rand_spec (GF : BundledGFunctors) [conerisGS GF] where
  -- * Operations
  rand_allocate_tape : val
  rand_tape : val
  -- * Ghost state
  /-- The assumptions about `Σ`. -/
  randG : BundledGFunctors → Type
  -- * Predicates
  rand_tapes (L : randG GF) (α : val) (ns : ℕ × List ℕ) : IProp GF
  -- * General properties of the predicates
  rand_tapes_timeless (L : randG GF) (α : val) (ns : ℕ × List ℕ) : Timeless (rand_tapes L α ns)
  rand_tapes_exclusive (L : randG GF) (α : val) (ns ns' : ℕ × List ℕ) :
    ⊢ rand_tapes L α ns -∗ rand_tapes L α ns' -∗ False
  rand_tapes_valid (L : randG GF) (α : val) (tb : ℕ) (ns : List ℕ) :
    ⊢ rand_tapes L α (tb, ns) -∗ ⌜∀ n ∈ ns, n ≤ tb⌝
  rand_tapes_presample (L : randG GF) (E : CoPset) (α : val) (tb : ℕ) (ns : List ℕ)
    (ε : ℝ≥0∞) (ε2 : Fin (tb + 1) → ℝ≥0∞) (Hsum : ∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢ rand_tapes L α (tb, ns) -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ rand_tapes L α (tb, ns ++ [(n : ℕ)]))
  -- * Program specs
  rand_allocate_tape_spec (L : randG GF) (E : CoPset) (tb : ℕ) :
    {{ True }} cpl(v(&rand_allocate_tape) #tb) @ E {{ v, RET v; rand_tapes L v (tb, []) }}
  rand_tape_spec_some (L : randG GF) (E : CoPset) (α : val) (tb n : ℕ) (ns : List ℕ) :
    {{ rand_tapes L α (tb, n :: ns) }} cpl(v(&rand_tape) v(&α) #tb) @ E
    {{ RET LitV (LitInt (n : ℤ)); rand_tapes L α (tb, ns) }}

/-- Rocq: `#[global] rand_tapes_timeless` (the instance). -/
instance rand_spec_rand_tapes_timeless {GF : BundledGFunctors} [conerisGS GF] [r : rand_spec GF]
    (L : r.randG GF) (α : val) (ns : ℕ × List ℕ) : Timeless (r.rand_tapes L α ns) :=
  r.rand_tapes_timeless L α ns

/-! ## Instantiate rand -/

section impl

/-- Rocq: `randG1`. -/
class randG1 (GF : BundledGFunctors) : Type

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `rand_allocate_tape` of `rand_spec1`. -/
def rand_allocate_tape1 : val := cpl_val(λ N, alloc(N))

/-- Rocq: `rand_tape` of `rand_spec1`. -/
def rand_tape1 : val := cpl_val(λ α N, rand(α) N)

/-- Rocq: `rand_tapes` of `rand_spec1`. -/
def rand_tapes1 (α : val) (ns : ℕ × List ℕ) : IProp GF :=
  iprop(∃ α' : Loc, ⌜α = LitV (LitLbl α')⌝ ∗ α' ↪N (ns.1; ns.2))

instance rand_tapes1_timeless (α : val) (ns : ℕ × List ℕ) :
    Timeless (rand_tapes1 (GF := GF) α ns) := by
  unfold rand_tapes1; infer_instance

/-- Rocq: first `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_tapes_exclusive (α : val) (ns ns' : ℕ × List ℕ) :
    ⊢@{IProp GF} rand_tapes1 α ns -∗ rand_tapes1 α ns' -∗ False := by
  unfold rand_tapes1
  iintro ⟨%a1, %h1, H1⟩ ⟨%a2, %h2, H2⟩
  rw [h1] at h2
  cases h2
  iapply tapeN_tapeN_contradict $$ H1 H2

/-- Rocq: second `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_tapes_valid (α : val) (tb : ℕ) (ns : List ℕ) :
    ⊢@{IProp GF} rand_tapes1 α (tb, ns) -∗ ⌜∀ n ∈ ns, n ≤ tb⌝ := by
  unfold rand_tapes1
  iintro ⟨%a, -, H⟩
  iapply tapeN_ineq $$ H

/-- Rocq: third `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_tapes_presample (E : CoPset) (α : val) (tb : ℕ) (ns : List ℕ)
    (ε : ℝ≥0∞) (ε2 : Fin (tb + 1) → ℝ≥0∞) (Hsum : ∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢@{IProp GF} rand_tapes1 α (tb, ns) -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ rand_tapes1 α (tb, ns ++ [(n : ℕ)])) := by
  unfold rand_tapes1
  iintro ⟨%a, %h, H⟩ Herr
  imod state_update_presample_exp E a tb ns ε ε2 Hsum $$ H Herr with ⟨%n, H, Herr⟩
  imodintro
  iexists n
  iframe Herr
  iexists a
  iframe H
  ipureintro
  exact h

/-- Rocq: fourth `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_allocate_tape_spec (E : CoPset) (tb : ℕ) :
    {{ True }} cpl(v(&rand_allocate_tape1) #tb) @ E
    {{ v, RET v; rand_tapes1 (GF := GF) v (tb, []) }} := by
  iintro %Φ - HΦ
  wp_lam
  wp_alloctape α as Hα
  iapply HΦ
  unfold rand_tapes1
  iexists α
  iframe Hα
  ipureintro
  rfl

/-- Rocq: fifth `Next Obligation` of `rand_spec1`. -/
theorem rand_spec1_rand_tape_spec_some (E : CoPset) (α : val) (tb n : ℕ) (ns : List ℕ) :
    {{ rand_tapes1 (GF := GF) α (tb, n :: ns) }} cpl(v(&rand_tape1) v(&α) #tb) @ E
    {{ RET LitV (LitInt (n : ℤ)); rand_tapes1 α (tb, ns) }} := by
  unfold rand_tapes1
  iintro %Φ ⟨%a, %h, Hα⟩ HΦ
  subst h
  dsimp only
  wp_rec
  wp_pures
  wp_randtape as %_
  iapply HΦ
  iexists a
  iframe Hα
  ipureintro
  rfl

/-- Rocq: `rand_spec1` (a `#[local] Program Definition`). -/
@[instance_reducible]
def rand_spec1 : rand_spec GF where
  rand_allocate_tape := rand_allocate_tape1
  rand_tape := rand_tape1
  randG := randG1
  rand_tapes _ α ns := rand_tapes1 α ns
  rand_tapes_timeless _ α ns := rand_tapes1_timeless α ns
  rand_tapes_exclusive _ := rand_spec1_rand_tapes_exclusive
  rand_tapes_valid _ := rand_spec1_rand_tapes_valid
  rand_tapes_presample _ := rand_spec1_rand_tapes_presample
  rand_allocate_tape_spec _ := rand_spec1_rand_allocate_tape_spec
  rand_tape_spec_some _ := rand_spec1_rand_tape_spec_some

end impl

/-! ## Checks -/

section checks

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF] (L : r1.randG GF)

/-- Rocq: `wp_rand_tape_1`. -/
theorem wp_rand_tape_1 (N : ℕ) (E : CoPset) (n : ℕ) (ns : List ℕ) (α : val) :
    {{ ▷ r1.rand_tapes L α (N, n :: ns) }} cpl(v(&r1.rand_tape) v(&α) #N) @ E
    {{ RET LitV (LitInt (n : ℤ)); r1.rand_tapes L α (N, ns) ∗ ⌜n ≤ N⌝ }} := by
  iintro %Φ >Hfrag HΦ
  ihave %H' := r1.rand_tapes_valid L α N (n :: ns) $$ Hfrag
  wp_apply r1.rand_tape_spec_some L E α N n ns $$ Hfrag with H
  iapply HΦ
  iframe H
  ipureintro
  exact H' n List.mem_cons_self

/-- Rocq: `wp_presample_adv_comp_rand_tape`. -/
theorem wp_presample_adv_comp_rand_tape (N : ℕ) (E : CoPset) (α : val) (ns : List ℕ)
    (ε1 : ℝ≥0∞) (ε2 : Fin (N + 1) → ℝ≥0∞) (Hsum : ∑' n, 1 / ((N : ℝ≥0∞) + 1) * ε2 n ≤ ε1) :
    ⊢ ▷ r1.rand_tapes L α (N, ns) -∗ ↯ ε1 -∗
      wp_update E iprop(∃ n : Fin (N + 1), ↯ (ε2 n) ∗ r1.rand_tapes L α (N, ns ++ [(n : ℕ)])) := by
  iintro >Htape Herr
  iapply wp_update_state_update
  iapply r1.rand_tapes_presample L E α N ns ε1 ε2 Hsum $$ Htape Herr

end checks

end Coneris.Lib.HocapRand
