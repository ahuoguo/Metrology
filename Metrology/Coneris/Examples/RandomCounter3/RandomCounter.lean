module

public import Metrology.Coneris.ErrorRules
public import Iris.Algebra.Lib.FracAuth
public import Iris.Algebra.Numbers

/-!
# An abstract random counter (version 3)

Ported from clutch/theories/coneris/examples/random_counter3/random_counter.v

## Rocq → Lean mapping
* `Class random_counter `{!conerisGS Σ} := RandCounter {...}` is the Lean
  `class random_counter GF` (over `[conerisGS GF]`) with the same field names:
  `new_counter`, `incr_counter`, `read_counter`, `counterG`, `counter_name`, `is_counter`,
  `counter_content_auth`, `counter_content_frag`, `is_counter_persistent`,
  `counter_content_auth_timeless`, `counter_content_frag_timeless`,
  `counter_content_auth_exclusive`, `counter_content_less_than`,
  `counter_content_frag_combine`, `counter_content_agree`, `counter_content_update`,
  `new_counter_spec`, `incr_counter_spec`, `read_counter_spec`.
  - As in `Coneris.Lib.HocapRand`, the implicit `{L : counterG Σ}` (Rocq finds it by type class
    search) is an explicit argument `(L : counterG GF)`.
  - The `#[global] ... ::` instance fields are fields, re-exported as the global instances
    `random_counter_is_counter_persistent`, `random_counter_counter_content_auth_timeless`,
    `random_counter_counter_content_frag_timeless`.
  - `frac` is iris-lean's `Qp`; `(f + f')%Qp` is `f + f'`, `1%Qp` is `1`.
  - `P -∗ Q` / `P ==∗ Q` fields are stated as `⊢ P -∗ Q` / `⊢ P ==∗ Q`; the `≡` of
    `counter_content_frag_combine` is `⊣⊢`.
  - Errors are `ℝ≥0∞`: the hypothesis `⌜∀ x, 0 <= ε2 x⌝` of `incr_counter_spec` is dropped;
    `SeriesC (λ n, 1 / 4 * ε2 n) <= ε` is `∑' n, 1 / 4 * ε2 n ≤ ε`; `fin 4` is `Fin 4` and the
    implicit coercion `fin_to_nat n` is `(n : ℕ)`. The type of `Q` (Rocq: `_ -> _ -> nat -> nat
    -> iProp Σ`, the holes being `R` and `fin 4 -> R`) is
    `ℝ≥0∞ → (Fin 4 → ℝ≥0∞) → ℕ → ℕ → IProp GF`.
  - `E∖↑N` is `E \ ↑N`.
  - Texan triples `{{{ P }}} e @ E {{{ x, RET v; Q }}}` are iris-lean's
    `{{ P }} e @ E {{ x, RET v; Q }}`; `RET (#z, #n)` is `RET cpl_val((#z, #n))`, `RET #n'` is
    `RET LitV (LitInt n')`.
* Section `lemmas`: `incr_counter_spec_seq` (same name), for `[rc : random_counter GF]` and
  `(L : rc.counterG GF)`. The hypothesis `(∀ n, 0 <= ε2 n)` is dropped (`ℝ≥0∞`);
  `((ε2 0 + ε2 1 + ε2 2 + ε2 3) / 4 <= ε)` is kept literally (`ℝ≥0∞` division by `4 ≠ 0`).
  `⌜(0<=n<4)%nat⌝` is `⌜0 ≤ n ∧ n < 4⌝`.

## Added
* `frac_auth_natF` (the functor of `inG Σ (frac_authR natR)`, shared by the three
  implementations) and the helpers `frac_auth_nat_auth_exclusive`,
  `frac_auth_nat_less_than`, `frac_auth_nat_frag_combine`, `frac_auth_nat_agree`,
  `frac_auth_nat_update` (the common proofs of the `Next Obligation`s of `random_counter1`,
  `random_counter2`, `random_counter3`).
* `quarter_sum_le` (the Rocq `rewrite SeriesC_finite_foldr/=. lra.` of
  `incr_counter_spec_seq`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE CMRA Prob ConProbLang ConProbLang.con_prob_lang
open Coneris

namespace Coneris.Examples.RandomCounter3.RandomCounter

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
  counter_content_auth (L : counterG GF) (γ : counter_name) (z : ℕ) : IProp GF
  counter_content_frag (L : counterG GF) (γ : counter_name) (f : Qp) (z : ℕ) : IProp GF
  -- * General properties of the predicates
  is_counter_persistent (L : counterG GF) (N : Namespace) (c : val) (γ1 : counter_name) :
    Persistent (is_counter L N c γ1)
  counter_content_auth_timeless (L : counterG GF) (γ : counter_name) (z : ℕ) :
    Timeless (counter_content_auth L γ z)
  counter_content_frag_timeless (L : counterG GF) (γ : counter_name) (f : Qp) (z : ℕ) :
    Timeless (counter_content_frag L γ f z)
  counter_content_auth_exclusive (L : counterG GF) (γ : counter_name) (z1 z2 : ℕ) :
    ⊢ counter_content_auth L γ z1 -∗ counter_content_auth L γ z2 -∗ False
  counter_content_less_than (L : counterG GF) (γ : counter_name) (z z' : ℕ) (f : Qp) :
    ⊢ counter_content_auth L γ z -∗ counter_content_frag L γ f z' -∗ ⌜z' ≤ z⌝
  counter_content_frag_combine (L : counterG GF) (γ : counter_name) (f f' : Qp) (z z' : ℕ) :
    iprop(counter_content_frag L γ f z ∗ counter_content_frag L γ f' z') ⊣⊢
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
    (γ1 : counter_name) (Q : ℝ≥0∞ → (Fin 4 → ℝ≥0∞) → ℕ → ℕ → IProp GF) :
    ↑N ⊆ E →
    {{ is_counter L N c γ1 ∗
        |={E \ ↑N, ∅}=>
          (∃ (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞),
            ↯ ε ∗ ⌜∑' n, 1 / 4 * ε2 n ≤ ε⌝ ∗
            (∀ n : Fin 4, ↯ (ε2 n) ={∅, E \ ↑N}=∗
              (∀ z : ℕ, counter_content_auth L γ1 z ={E \ ↑N}=∗
                counter_content_auth L γ1 (z + n) ∗ Q ε ε2 z n))) }}
      cpl(v(&incr_counter) v(&c)) @ E
    {{ (z n : ℕ), RET cpl_val((#z, #n)); ∃ ε ε2, Q ε ε2 z n }}
  read_counter_spec (L : counterG GF) (N : Namespace) (E : CoPset) (c : val)
    (γ1 : counter_name) (Q : ℕ → IProp GF) :
    ↑N ⊆ E →
    {{ is_counter L N c γ1 ∗
        (∀ z : ℕ, counter_content_auth L γ1 z ={E \ ↑N}=∗ counter_content_auth L γ1 z ∗ Q z) }}
      cpl(v(&read_counter) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt (n' : ℤ)); Q n' }}

section instances

variable {GF : BundledGFunctors} [conerisGS GF] [rc : random_counter GF]

/-- Rocq: `#[global] is_counter_persistent` (the instance). -/
instance random_counter_is_counter_persistent (L : rc.counterG GF) (N : Namespace) (c : val)
    (γ1 : rc.counter_name) : Persistent (rc.is_counter L N c γ1) :=
  rc.is_counter_persistent L N c γ1

/-- Rocq: `#[global] counter_content_auth_timeless` (the instance). -/
instance random_counter_counter_content_auth_timeless (L : rc.counterG GF)
    (γ : rc.counter_name) (z : ℕ) : Timeless (rc.counter_content_auth L γ z) :=
  rc.counter_content_auth_timeless L γ z

/-- Rocq: `#[global] counter_content_frag_timeless` (the instance). -/
instance random_counter_counter_content_frag_timeless (L : rc.counterG GF)
    (γ : rc.counter_name) (f : Qp) (z : ℕ) : Timeless (rc.counter_content_frag L γ f z) :=
  rc.counter_content_frag_timeless L γ f z

end instances

/-! ## Shared ghost-state helpers (`frac_authR natR`) -/

/-- Helper: the functor of `inG Σ (frac_authR natR)`. -/
abbrev frac_auth_natF : COFE.OFunctorPre := constOF (FracAuth (A := Nat))

section frac_auth_nat

variable {GF : BundledGFunctors} [ElemG GF frac_auth_natF]

/-- Helper: first `Next Obligation` of `random_counter1/2/3` (`counter_content_auth_exclusive`). -/
theorem frac_auth_nat_auth_exclusive (γ : GName) (z1 z2 : ℕ) :
    ⊢@{IProp GF} iOwn (F := frac_auth_natF) γ (●F z1) -∗
      iOwn (F := frac_auth_natF) γ (●F z2) -∗ False := by
  iintro H1 H2
  icombine H1 H2 gives %H
  exact (FracAuth.auth_op_valid H).elim

/-- Helper: second `Next Obligation` of `random_counter1/2/3` (`counter_content_less_than`). -/
theorem frac_auth_nat_less_than (γ : GName) (z z' : ℕ) (f : Qp) :
    ⊢@{IProp GF} iOwn (F := frac_auth_natF) γ (●F z) -∗
      iOwn (F := frac_auth_natF) γ (◯F{f} z') -∗ ⌜z' ≤ z⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  have ⟨w, hw⟩ := CommMonoidLike.included_iff.mp (FracAuth.included_total H)
  have : z = z' + w := hw
  omega

/-- Helper: third `Next Obligation` of `random_counter1/2/3` (`counter_content_frag_combine`). -/
theorem frac_auth_nat_frag_combine (γ : GName) (f f' : Qp) (z z' : ℕ) :
    iprop(iOwn (F := frac_auth_natF) γ (◯F{f} z) ∗ iOwn (F := frac_auth_natF) γ (◯F{f'} z'))
      ⊣⊢@{IProp GF} iOwn (F := frac_auth_natF) γ (◯F{f + f'} (z + z')) := by
  rw [← iOwn_op.to_eq]
  exact (congrArg (iOwn (F := frac_auth_natF) γ) FracAuth.frag_op).to_bi.symm

/-- Helper: fourth `Next Obligation` of `random_counter1/2/3` (`counter_content_agree`). -/
theorem frac_auth_nat_agree (γ : GName) (z z' : ℕ) :
    ⊢@{IProp GF} iOwn (F := frac_auth_natF) γ (●F z) -∗
      iOwn (F := frac_auth_natF) γ (◯F{1} z') -∗ ⌜z' = z⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact (FracAuth.agree H).symm

/-- Helper: fifth `Next Obligation` of `random_counter1/2/3` (`counter_content_update`). -/
theorem frac_auth_nat_update (γ : GName) (f : Qp) (z1 z2 z3 : ℕ) :
    ⊢@{IProp GF} iOwn (F := frac_auth_natF) γ (●F z1) -∗
      iOwn (F := frac_auth_natF) γ (◯F{f} z2) ==∗
      iOwn (F := frac_auth_natF) γ (●F (z1 + z3)) ∗
      iOwn (F := frac_auth_natF) γ (◯F{f} (z2 + z3)) := by
  iintro H1 H2
  imod iOwn_update_op (a' := CMRA.op (●F (z1 + z3)) (◯F{f} (z2 + z3))) $$ [$H1 $H2]
    with ⟨H1, H2⟩
  · exact FracAuth.update (CommMonoidLike.leftCancelAdd_local_update
      (by show z1 + (z2 + z3) = (z1 + z3) + z2; omega))
  imodintro
  iframe

end frac_auth_nat

/-! ## Lemmas -/

/-- Helper: `∑ n : fin 4, 1/4 * ε2 n = (ε2 0 + ε2 1 + ε2 2 + ε2 3) / 4` (Rocq:
`rewrite SeriesC_finite_foldr/=. lra.`). -/
theorem quarter_sum_le (ε2 : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (Hineq : (ε2 0 + ε2 1 + ε2 2 + ε2 3) / 4 ≤ ε) :
    ∑' n : Fin 4, 1 / 4 * ε2 (n : ℕ) ≤ ε := by
  rw [tsum_fintype, ← Finset.mul_sum, Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [ENNReal.div_eq_inv_mul] at Hineq
  rw [one_div]
  exact Hineq

section lemmas

variable {GF : BundledGFunctors} [conerisGS GF] [rc : random_counter GF] (L : rc.counterG GF)

/-- Rocq: `incr_counter_spec_seq`. -/
theorem incr_counter_spec_seq (N : Namespace) (E : CoPset) (c : val) (γ1 : rc.counter_name)
    (ε : ℝ≥0∞) (ε2 : ℕ → ℝ≥0∞) (q : Qp) (z : ℕ) (Hsubset : ↑N ⊆ E)
    (Hineq : (ε2 0 + ε2 1 + ε2 2 + ε2 3) / 4 ≤ ε) :
    {{ rc.is_counter L N c γ1 ∗ ↯ ε ∗ rc.counter_content_frag L γ1 q z }}
      cpl(v(&rc.incr_counter) v(&c)) @ E
    {{ (z' n : ℕ), RET cpl_val((#z', #n)); ⌜0 ≤ n ∧ n < 4⌝ ∗ ⌜z ≤ z'⌝ ∗ ↯ (ε2 n) ∗
        rc.counter_content_frag L γ1 q (z + n) }} := by
  iintro %Φ ⟨#Hinv, Herr, Hcontent⟩ HΦ
  wp_apply rc.incr_counter_spec L N E c γ1
    (fun _ _ z' n => iprop(⌜0 ≤ n ∧ n < 4⌝ ∗ ⌜z ≤ z'⌝ ∗ ↯ (ε2 n) ∗
      rc.counter_content_frag L γ1 q (z + n))) Hsubset $$ [Herr Hcontent]
    with %z' %n ⟨%ε', %ε2', H⟩
  · isplit
    · iexact Hinv
    iapply fupd_mask_intro (by exact LawfulSet.empty_subset)
    iintro Hclose
    iexists ε, (fun x => ε2 (x : ℕ))
    iframe Herr
    isplit
    · ipureintro
      exact quarter_sum_le ε2 ε Hineq
    iintro %n Herr
    imod Hclose
    imodintro
    iintro %z'' Hauth
    ihave %Hle := rc.counter_content_less_than L γ1 z'' z q $$ Hauth Hcontent
    imod rc.counter_content_update L γ1 q z'' z n $$ Hauth Hcontent with ⟨Hauth, Hfrag⟩
    imodintro
    iframe
    ipureintro
    exact ⟨⟨Nat.zero_le _, n.isLt⟩, Hle⟩
  iapply HΦ $$ H

end lemmas

end Coneris.Examples.RandomCounter3.RandomCounter
