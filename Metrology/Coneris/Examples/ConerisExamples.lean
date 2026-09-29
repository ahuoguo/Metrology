module

public import Metrology.Coneris.ErrorRules

/-!
# Small Coneris examples

Ported from clutch/theories/coneris/examples/coneris_examples.v

## Rocq → Lean map
* Namespace `Coneris.Examples.ConerisExamples`. All names are kept: `φ`, `loop`, `e'`, `e`,
  `loop_lemma`, `wp_e'_two`, `wp_e'_three`, `wp_e` (section `test`); `foo`, `wp_foo`, `bar`,
  `wp_bar`, `baz`, `wp_baz`, `fork_prog`, `wp_fork`, `wp_concurrency_atomic` (section `foo`).
  `wp_fork` shadows the core `Coneris.wp_fork` inside this namespace (the proof uses the core one
  as `Coneris.wp_fork`).
* `conerisGS Σ` is `[conerisGS GF]`. Programs are transcribed with the `cpl` notation
  (`rand #N` is `rand(#N)`, `loop #()` is `&loop #()`, `e' "n"` is `&(e' "n")`).
* Errors are `ℝ≥0∞`: `nnreal_half` is `1 / 2`, `nnreal_div (nnreal_nat 1) (nnreal_nat 4)` is
  `1 / 4`, `nnreal_inv (nnreal_nat 2)` is `2⁻¹`, `/ (N + 1)` is `((N : ℝ≥0∞) + 1)⁻¹`; the error
  functions `ε2`/`f` are `ℝ≥0∞`-valued (their nonnegativity side goals vanish). None of these
  involve truncated subtraction or division by zero.
* `{{{ P }}} e @ E {{{ v, RET v; Q }}}` is iris-lean's `{{ P }} e @ E {{ v, RET v; Q }}`;
  `wp_bar` is a `Definition` in Rocq and a `theorem` here.

## Proofs that differ from Rocq
* The `inv_fin`/`destruct (fin_to_nat x)` case analyses on samples are `Fin.ext`/`fin_cases`
  followed by `rcases .. rfl`; `case_bool_decide` is `rw [decide_eq_true ..]` /
  `rw [decide_eq_false ..]` on the evaluated comparison, so that `wp_pures` can take the `if`.
* The sums `SeriesC_finite_foldr ..; lra` are `Fin.sum_univ_*` plus `norm_num` (and the helper
  `baz_sum`).
* In `wp_e`, the substituted program `subst "n" #n (e' "n")` is folded back to `e' #n` with the
  helper `e'_subst` (Rocq does this by computation).
* In `wp_baz` the Löb induction generalizes the error credit (`iloeb as IH generalizing Herr`),
  as Rocq's `iLöb` does implicitly for the spatial context.

## Added
`e'_subst`, `baz_sum` (helpers).

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris

namespace Coneris.Examples.ConerisExamples

/-! ## Section `test` -/

section test

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `φ`. -/
def φ (v : val) : IProp GF := iprop(⌜v = LitV (LitBool true)⌝)

/-- Rocq: `loop`. -/
def loop : val := cpl_val(rec loop x := loop x)

/-- Rocq: `e'`. -/
def e' (n : expr) : expr := cpl(
  let k := rand(#1) in
  if &n + k ≤ #2 then
    #true
  else
    if &n + k = #3
    then #false
    else &loop #())

/-- Rocq: `e`. -/
def e : expr := cpl(
  let n := rand(#3) in
  if n ≤ #1
  then #true
  else &(e' "n"))

/-- Helper: substituting into `e' "n"`. -/
theorem e'_subst (v : val) : subst "n" v (e' (Var "n")) = e' (Val v) := rfl

/-- Rocq: `loop_lemma`. -/
theorem loop_lemma (E : CoPset) (v : val) (Φ : val → IProp GF) :
    ⊢ WP (App (Val loop) (Val v)) @ E {{ Φ }} := by
  iloeb as IH
  wp_rec
  iexact IH

/-- Rocq: `wp_e'_two`. -/
theorem wp_e'_two (E : CoPset) :
    ⊢@{IProp GF} ↯ (1 / 2) -∗ WP (e' (Val (LitV (LitInt 2)))) @ E {{ φ }} := by
  iintro Herr
  unfold e'
  wp_apply wp_rand_err_nat 1 1 1 rfl
  isplitl
  · iapply ErrorCredit.ext _ $$ Herr
    norm_num
  · iintro %x %Hx
    obtain rfl : x = 0 := Fin.ext (by have := x.isLt; simp only [Fin.val_zero]; omega)
    simp only [Fin.val_zero, Nat.cast_zero]
    wp_pures
    unfold φ
    ipureintro
    rfl

/-- Rocq: `wp_e'_three`. -/
theorem wp_e'_three (E : CoPset) :
    ⊢@{IProp GF} ↯ (1 / 2) -∗ WP (e' (Val (LitV (LitInt 3)))) @ E {{ φ }} := by
  iintro Herr
  unfold e'
  wp_apply wp_rand_err_nat 1 1 0 rfl
  isplitl
  · iapply ErrorCredit.ext _ $$ Herr
    norm_num
  · iintro %x %Hx
    obtain rfl : x = 1 := Fin.ext (by have := x.isLt; simp only [Fin.val_one]; omega)
    simp only [Fin.val_one, Nat.cast_one]
    wp_pures
    iapply loop_lemma

/-- Rocq: `wp_e`. -/
theorem wp_e (E : CoPset) :
    ⊢@{IProp GF} ↯ (1 / 4) -∗ WP e @ E {{ φ }} := by
  iintro Herr
  unfold e
  let ε2 : Fin (3 + 1) → ℝ≥0∞ := fun n => if (n : ℕ) < 2 then 0 else 2⁻¹
  wp_apply wp_couple_rand_adv_comp1 3 3 _ ε2 rfl ?_ $$ Herr with %n Herr
  · rw [tsum_fintype, Fin.sum_univ_four]
    simp only [ε2]
    norm_num
    rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
  wp_pures
  by_cases hn : (n : ℕ) ≤ 1
  · have : ((n : ℕ) : ℤ) ≤ 1 := by omega
    rw [decide_eq_true hn]
    wp_pures
    unfold φ
    ipureintro
    rfl
  · have : ¬ ((n : ℕ) : ℤ) ≤ 1 := by omega
    rw [decide_eq_false hn]
    wp_pures
    rw [e'_subst]
    have hn' : (n : ℕ) = 2 ∨ (n : ℕ) = 3 := by have := n.isLt; omega
    rcases hn' with hn' | hn'
    · simp only [ε2, hn', show ¬ (2 < 2) from by omega, ↓reduceIte]
      iapply wp_e'_two
      iapply ErrorCredit.ext _ $$ Herr
      norm_num
    · simp only [ε2, hn', show ¬ (3 < 2) from by omega, ↓reduceIte]
      iapply wp_e'_three
      iapply ErrorCredit.ext _ $$ Herr
      norm_num

end test

/-! ## Section `foo` -/

section foo

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `foo`. -/
def foo (N m : ℕ) : expr := cpl(
  let n := rand(#N) in
  if n = #m then #false else #true)

/-- Rocq: `wp_foo`. -/
theorem wp_foo (N m : ℕ) (E : CoPset) :
    {{ ↯ ((N : ℝ≥0∞) + 1)⁻¹ }} (foo N m) @ E
    {{ v, RET v; (⌜v = LitV (LitBool true)⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold foo
  wp_bind (Rand _ _)
  wp_apply wp_rand_err_nat N N m (by simp)
  iframe Herr
  iintro %x %Hx
  wp_pures
  rw [decide_eq_false Hx]
  wp_if_false
  iapply HΦ
  ipureintro
  rfl

/-- Rocq: `bar`. -/
def bar (N : ℕ) : expr := cpl(
  let m := rand(#N) in
  let n := rand(#N) in
  if n = m then #false else #true)

/-- Rocq: `wp_bar` (a `Definition` in Rocq). -/
theorem wp_bar (N : ℕ) (E : CoPset) :
    {{ ↯ ((N : ℝ≥0∞) + 1)⁻¹ }} (bar N) @ E
    {{ v, RET v; (⌜v = LitV (LitBool true)⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold bar
  wp_bind (Rand _ _)
  wp_apply wp_rand N N (by simp) $$ [] with %m -
  · itrivial
  wp_pures
  wp_apply wp_rand_err_nat N N m (by simp)
  iframe Herr
  iintro %x %Hx
  wp_pures
  rw [decide_eq_false Hx]
  wp_if_false
  iapply HΦ
  ipureintro
  rfl

/-- Rocq: `baz`. -/
def baz : expr := cpl(
  rec baz x :=
    let n := rand(#2) in
    (if n < #2
      then n
      else baz #()))

/-- Helper: the mean of the error function of `wp_baz` (Rocq: `SeriesC_finite_foldr; lra`). -/
theorem baz_sum : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ * 2⁻¹ = 2⁻¹ := by
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

/-- Rocq: `wp_baz`. -/
theorem wp_baz (E : CoPset) :
    ⊢@{IProp GF} ↯ (2 : ℝ≥0∞)⁻¹ -∗ WP (App baz (Val (LitV LitUnit))) @ E
      {{ v, ⌜v = LitV (LitInt 0)⌝ }} := by
  iintro Herr
  unfold baz
  wp_pure
  iloeb as IH generalizing Herr
  wp_pures
  let f : Fin (2 + 1) → ℝ≥0∞ := fun n => if n = 0 then 0 else if n = 1 then 1 else 2⁻¹
  wp_apply wp_couple_rand_adv_comp 2 2 _ f rfl ?_ $$ Herr with %n Herr
  · rw [tsum_fintype, Fin.sum_univ_three]
    simp only [f]
    norm_num
    exact baz_sum
  wp_pures
  have h3 : n = 0 ∨ n = 1 ∨ n = 2 := by fin_cases n <;> simp
  rcases h3 with rfl | rfl | rfl
  · simp only [f, Fin.val_zero, Nat.cast_zero, zero_le, _root_.decide_true, ↓reduceIte]
    wp_pures
    ipureintro
    rfl
  · simp only [f, Fin.val_one, Nat.cast_one, le_refl, _root_.decide_true, ↓reduceIte, one_ne_zero]
    iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Herr
  · simp only [f, Fin.val_two, Nat.cast_ofNat]
    simp
    wp_if_false
    iapply IH $$ Herr

/-- Rocq: `fork_prog`. -/
def fork_prog : expr := cpl(fork(#()); #())

/-- Rocq: `wp_fork` (shadows `Coneris.wp_fork` inside this namespace). -/
theorem wp_fork : {{ True }} fork_prog {{ v, RET v; (True : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold fork_prog
  wp_apply Coneris.wp_fork
  · wp_pures
    itrivial
  · wp_pures
    iapply HΦ
    itrivial

/-- Rocq: `wp_concurrency_atomic`. -/
theorem wp_concurrency_atomic (l : Loc) :
    {{ l ↦ LitV (LitInt 0) }}
      cpl(cmpXchg(#l, #0, #1);
          cmpXchg(#l, #0, #1);
          xchg(#l, #2);
          faa(#l, #3))
    {{ RET LitV (LitInt 2); (l ↦ LitV (LitInt 5) : IProp GF) }} := by
  iintro %Φ Hl HΦ
  wp_cmpxchg_suc
  wp_pures
  wp_cmpxchg_fail
  wp_pures
  wp_xchg
  wp_pures
  wp_faa
  iapply HΦ $$ Hl

end foo

end Coneris.Examples.ConerisExamples
