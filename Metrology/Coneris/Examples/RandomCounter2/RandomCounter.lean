module

public import Metrology.Coneris.ErrorRules

/-!
# An abstract random counter

Ported from clutch/theories/coneris/examples/random_counter2/random_counter.v

## Rocq → Lean mapping
* `Class random_counter `{!conerisGS Σ} := RandCounter {...}` is the Lean
  `class random_counter GF` (over `[conerisGS GF]`) with the same field names: `new_counter`,
  `incr_counter`, `read_counter`, `counterG`, `counter_name`, `is_counter`, `counter_tapes`,
  `counter_content_auth`, `counter_content_frag`, `is_counter_persistent`,
  `counter_tapes_timeless`, `counter_content_auth_timeless`, `counter_content_frag_timeless`,
  `counter_tapes_presample`, `counter_content_auth_exclusive`, `counter_content_less_than`,
  `counter_content_frag_combine`, `counter_content_agree`, `counter_content_update`,
  `new_counter_spec`, `incr_counter_spec`, `read_counter_spec`.
  - As in `Coneris.Lib.HocapRand`, the implicit `{L : counterG Σ}` is an explicit argument
    `(L : counterG GF)`.
  - The `#[global] ... ::` instance fields are fields, re-exported as the global instances
    `random_counter_is_counter_persistent`, `random_counter_counter_tapes_timeless`,
    `random_counter_counter_content_auth_timeless`,
    `random_counter_counter_content_frag_timeless`.
  - `frac` is iris-lean's `Qp`; `(f + f')%Qp` is `f + f'`.
  - Errors are `ℝ≥0∞`: the hypothesis `∀ x, 0 <= ε2 x` of `counter_tapes_presample` is
    dropped; `SeriesC (λ n, 1 / 4 * ε2 n) <= ε` (over `fin 4`) is
    `∑' n : Fin 4, 1 / 4 * ε2 n ≤ ε`; `fin_to_nat n` is `(n : ℕ)`.
  - `P -∗ Q` / `P ==∗ Q` fields are stated as `⊢ P -∗ Q` / `⊢ P ==∗ Q`; the `≡` of
    `counter_content_frag_combine` is `⊣⊢`.
  - Texan triples are iris-lean's `{{ P }} e @ E {{ x, RET v; Q }}`; `RET (#z, #n)` is
    `RET cpl_val((#z, #n))` and `RET #n'` is `RET LitV (LitInt n')` (for `z n n' : ℕ`).
* Section `lemmas`: `incr_counter_spec_seq` (same name), for `[rc : random_counter GF]`
  and `(L : rc.counterG GF)`. Errors are `ℝ≥0∞`: `(∀ n, 0 <= ε2 n)` is dropped.
  The Rocq proof pads `ε2` with `ε2'` (unused); it is not ported.

## Omitted
* The commented-out Rocq field `tape_name`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris

namespace Coneris.Examples.RandomCounter2.RandomCounter

/-- Rocq: `random_counter`. -/
class random_counter (GF : BundledGFunctors) [conerisGS GF] where
  -- * Operations
  new_counter : val
  incr_counter : val
  read_counter : val
  -- * Ghost state
  /-- The assumptions about `Σ`. -/
  counterG : BundledGFunctors → Type
  /-- `name` is used to associate `locked` with `is_lock`. -/
  counter_name : Type
  -- * Predicates
  is_counter (L : counterG GF) (N : Namespace) (counter : val) (γ : counter_name) : IProp GF
  counter_tapes (L : counterG GF) (α : val) (n : Option ℕ) : IProp GF
  counter_content_auth (L : counterG GF) (γ : counter_name) (z : ℕ) : IProp GF
  counter_content_frag (L : counterG GF) (γ : counter_name) (f : Qp) (z : ℕ) : IProp GF
  -- * General properties of the predicates
  is_counter_persistent (L : counterG GF) (N : Namespace) (c : val) (γ1 : counter_name) :
    Persistent (is_counter L N c γ1)
  counter_tapes_timeless (L : counterG GF) (α : val) (ns : Option ℕ) :
    Timeless (counter_tapes L α ns)
  counter_content_auth_timeless (L : counterG GF) (γ : counter_name) (z : ℕ) :
    Timeless (counter_content_auth L γ z)
  counter_content_frag_timeless (L : counterG GF) (γ : counter_name) (f : Qp) (z : ℕ) :
    Timeless (counter_content_frag L γ f z)
  counter_tapes_presample (L : counterG GF) (N : Namespace) (E : CoPset) (γ : counter_name)
    (c : val) (α : val) (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) :
    ↑N ⊆ E →
    ∑' n : Fin 4, 1 / 4 * ε2 n ≤ ε →
    ⊢ is_counter L N c γ -∗ counter_tapes L α none -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin 4, ↯ (ε2 n) ∗ counter_tapes L α (some (n : ℕ)))
  counter_content_auth_exclusive (L : counterG GF) (γ : counter_name) (z1 z2 : ℕ) :
    ⊢ counter_content_auth L γ z1 -∗ counter_content_auth L γ z2 -∗ False
  counter_content_less_than (L : counterG GF) (γ : counter_name) (z z' : ℕ) (f : Qp) :
    ⊢ counter_content_auth L γ z -∗ counter_content_frag L γ f z' -∗ ⌜z' ≤ z⌝
  counter_content_frag_combine (L : counterG GF) (γ : counter_name) (f f' : Qp) (z z' : ℕ) :
    (counter_content_frag L γ f z ∗ counter_content_frag L γ f' z') ⊣⊢
      counter_content_frag L γ (f + f') (z + z')
  counter_content_agree (L : counterG GF) (γ : counter_name) (z z' : ℕ) :
    ⊢ counter_content_auth L γ z -∗ counter_content_frag L γ 1 z' -∗ ⌜z' = z⌝
  counter_content_update (L : counterG GF) (γ : counter_name) (f : Qp) (z1 z2 z3 : ℕ) :
    ⊢ counter_content_auth L γ z1 -∗ counter_content_frag L γ f z2 ==∗
      counter_content_auth L γ (z1 + z3) ∗ counter_content_frag L γ f (z2 + z3)
  -- * Program specs
  new_counter_spec (L : counterG GF) (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter) #()) @ E
    {{ c, RET c; ∃ γ1, is_counter L N c γ1 ∗ counter_content_frag L γ1 1 0 }}
  incr_counter_spec (L : counterG GF) (N : Namespace) (E : CoPset) (c : val)
    (γ1 : counter_name) (Q : ℕ → ℕ → IProp GF) :
    ↑N ⊆ E →
    {{ is_counter L N c γ1 ∗
        (∀ α, counter_tapes L α none -∗
          state_update E E iprop(∃ n, counter_tapes L α (some n) ∗
            (∀ z : ℕ, counter_content_auth L γ1 z ={E \ ↑N}=∗
              counter_content_auth L γ1 (z + n) ∗ Q z n))) }}
      cpl(v(&incr_counter) v(&c)) @ E
    {{ (z n : ℕ), RET cpl_val((#z, #n)); Q z n }}
  read_counter_spec (L : counterG GF) (N : Namespace) (E : CoPset) (c : val)
    (γ1 : counter_name) (Q : ℕ → IProp GF) :
    ↑N ⊆ E →
    {{ is_counter L N c γ1 ∗
        (∀ z : ℕ, counter_content_auth L γ1 z ={E \ ↑N}=∗
          counter_content_auth L γ1 z ∗ Q z) }}
      cpl(v(&read_counter) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt n'); Q n' }}

section instances

variable {GF : BundledGFunctors} [conerisGS GF] [rc : random_counter GF]

/-- Rocq: `#[global] is_counter_persistent` (the instance). -/
instance random_counter_is_counter_persistent (L : rc.counterG GF) (N : Namespace) (c : val)
    (γ1 : rc.counter_name) : Persistent (rc.is_counter L N c γ1) :=
  rc.is_counter_persistent L N c γ1

/-- Rocq: `#[global] counter_tapes_timeless` (the instance). -/
instance random_counter_counter_tapes_timeless (L : rc.counterG GF) (α : val) (ns : Option ℕ) :
    Timeless (rc.counter_tapes L α ns) :=
  rc.counter_tapes_timeless L α ns

/-- Rocq: `#[global] counter_content_auth_timeless` (the instance). -/
instance random_counter_counter_content_auth_timeless (L : rc.counterG GF)
    (γ : rc.counter_name) (z : ℕ) : Timeless (rc.counter_content_auth L γ z) :=
  rc.counter_content_auth_timeless L γ z

/-- Rocq: `#[global] counter_content_frag_timeless` (the instance). -/
instance random_counter_counter_content_frag_timeless (L : rc.counterG GF)
    (γ : rc.counter_name) (f : Qp) (z : ℕ) : Timeless (rc.counter_content_frag L γ f z) :=
  rc.counter_content_frag_timeless L γ f z

end instances

section lemmas

variable {GF : BundledGFunctors} [conerisGS GF] [rc : random_counter GF] (L : rc.counterG GF)

/-- Rocq: `incr_counter_spec_seq`. -/
theorem incr_counter_spec_seq (N : Namespace) (E : CoPset) (c : val) (γ1 : rc.counter_name)
    (ε : ℝ≥0∞) (ε2 : ℕ → ℝ≥0∞) (q : Qp) (z : ℕ) (Hsubset : ↑N ⊆ E)
    (Hineq : (ε2 0 + ε2 1 + ε2 2 + ε2 3) / 4 ≤ ε) :
    {{ rc.is_counter L N c γ1 ∗ ↯ ε ∗ rc.counter_content_frag L γ1 q z }}
      cpl(v(&rc.incr_counter) v(&c)) @ E
    {{ (z' n : ℕ), RET cpl_val((#z', #n));
        ⌜0 ≤ n ∧ n < 4⌝ ∗ ⌜z ≤ z'⌝ ∗ ↯ (ε2 n) ∗ rc.counter_content_frag L γ1 q (z + n) }} := by
  iintro %Φ ⟨#Hinv, Herr, Hcontent⟩ HΦ
  wp_apply rc.incr_counter_spec L N E c γ1
    (fun z' n => iprop(⌜0 ≤ n ∧ n < 4⌝ ∗ ⌜z ≤ z'⌝ ∗ ↯ (ε2 n) ∗
      rc.counter_content_frag L γ1 q (z + n))) Hsubset $$ [Herr Hcontent] with %z' %n H
  · isplitr
    · iexact Hinv
    iintro %α Htape
    imod rc.counter_tapes_presample L N E γ1 c α ε (fun x => ε2 (x : ℕ)) Hsubset ?_
      $$ Hinv Htape Herr with ⟨%n, Herr, Htape⟩
    · rw [tsum_fintype, Fin.sum_univ_four]
      refine le_trans (le_of_eq ?_) Hineq
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
      rw [← mul_add, ← mul_add, ← mul_add, one_div, ENNReal.div_eq_inv_mul]
      rfl
    imodintro
    iexists (n : ℕ)
    iframe Htape
    iintro %z0 Hauth
    ihave %Hle := rc.counter_content_less_than L γ1 z0 z q $$ Hauth Hcontent
    imod rc.counter_content_update L γ1 q z0 z (n : ℕ) $$ Hauth Hcontent with ⟨Hauth, Hfrag⟩
    imodintro
    iframe Hauth Herr Hfrag
    ipureintro
    exact ⟨⟨Nat.zero_le _, n.isLt⟩, Hle⟩
  · iapply HΦ $$ H

end lemmas

end Coneris.Examples.RandomCounter2.RandomCounter
