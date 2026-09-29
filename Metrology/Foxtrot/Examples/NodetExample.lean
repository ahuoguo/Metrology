module

public import Metrology.Foxtrot.Lib.Nodet
public import Metrology.Foxtrot.Lib.Diverge
public import Metrology.Foxtrot.ErrorRules
public import Metrology.Foxtrot.BinaryRel.BinarySoundness
public import Metrology.Foxtrot.BinaryRel.BinaryRelTactics
public import Metrology.Foxtrot.AdequacyInstance

/-!
# A program with a nondeterministic sampling bound

Ported from clutch/theories/foxtrot/examples/nodet_example.v

`prog` samples uniformly from `0..n` for a nondeterministic `n` and diverges on `0`; it is
contextually equivalent to `#()` (the RHS can choose `n` arbitrarily large, so that the
probability of sampling `0` is below any given error budget).

## Rocq → Lean map
* `prog`, `prog_refines_unit`, `unit_refines_prog`, `prog_eq_unit`: same names (namespace
  `Foxtrot.Examples.NodetExample`).
* `rand "n"` is `rand("n")`; `if: .. then .. else ..` is `if .. then .. else ..`.
* `foxtrotRΣ` is `foxtrotSigma`, with the local instance `foxtrotRGpreS_foxtrotSigma`.

## Deviations
* Error credits are `ℝ≥0∞`-valued: Rocq's `archimed_cor1` (a `N` with `/N < ε`, `0 < N`)
  is `ENNReal.exists_inv_nat_lt` (a `N` with `N⁻¹ < ε`, where `0⁻¹ = ∞` makes `N = 0`
  impossible), and `/(S N) < ε` becomes `((N + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ε` (via
  `ENNReal.inv_le_inv`). `ec_weaken` is `ErrorCredit.weaken`; the `ec_eq` rewrite
  (`S_INR`, `plus_INR`) is not needed since `tp_rand_r_err` is stated with `((N + 1 : ℕ))⁻¹`.
* `case_bool_decide` is `by_cases h : m = 0` followed by `simp only [h, decide_true/false]`;
  `solve_vals_compare_safe` is discharged by `tp_pures`.
* The postcondition `False` of `wp_diverge` is eliminated with `%H` / `H.elim` (Rocq:
  `by iIntros`).

## Added
* `foxtrotRGpreS_foxtrotSigma` (Rocq: `subG_foxtrotRGPreS`).

## Omitted
None.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot Foxtrot.BinaryRel Foxtrot.Lib.Nodet Foxtrot.Lib.Diverge

namespace Foxtrot.Examples.NodetExample

/-- Rocq: `subG_foxtrotRGPreS` (at `foxtrotSigma`, Rocq's `foxtrotRΣ`). -/
local instance foxtrotRGpreS_foxtrotSigma : foxtrotRGpreS foxtrotSigma := ⟨inferInstance⟩

/-- Rocq: `prog`. -/
def prog : expr := cpl(
  let "n" := &nodet #() in
  if rand("n") = #0
  then &diverge #()
  else #())

/-- Rocq: `prog_refines_unit`. -/
theorem prog_refines_unit :
    (∅ : varmap type) ⊨ prog ≤ctx≤ cpl(#()) : TUnit := by
  refine refines_sound foxtrotSigma _ _ _ fun Δ => ?_
  unfold_rel
  iintro %K %j Hspec
  unfold prog
  wp_apply wp_nodet $$ [] with %n -
  · itrivial
  wp_pures
  wp_apply wp_rand n n (by simp) $$ [] with %m %Hm
  · itrivial
  wp_pures
  by_cases h : m = 0
  · simp only [h, decide_true]
    wp_pures
    wp_apply wp_diverge $$ [] with %v %H
    · itrivial
    exact H.elim
  · simp only [h, decide_false]
    wp_pure
    iexists _
    iframe Hspec
    dsimp only [interp, lrel_unit]
    ipureintro
    exact ⟨rfl, rfl⟩

/-- Rocq: `unit_refines_prog`. -/
theorem unit_refines_prog :
    (∅ : varmap type) ⊨ cpl(#()) ≤ctx≤ prog : TUnit := by
  refine refines_sound foxtrotSigma _ _ _ fun Δ => ?_
  unfold_rel
  iintro %K %j Hspec
  unfold prog
  imod pupd_epsilon_err ⊤ with ⟨%ε, %Hpos, Herr⟩
  obtain ⟨N, HN⟩ := ENNReal.exists_inv_nat_lt Hpos.ne'
  have Hineq' : ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ε :=
    le_of_lt (lt_of_le_of_lt (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ N)) HN)
  ihave Herr := ErrorCredit.weaken Hineq' $$ Herr
  tp_bind j (App (Val nodet) _)
  imod tp_nodet j _ ⊤ N $$ Hspec with Hspec
  tp_pures j
  tp_bind j (Rand _ _)
  imod tp_rand_r_err N N ⊤ _ j 0 (by simp) $$ Hspec Herr with ⟨%n, %Hn, %Hn0, Hspec⟩
  tp_pures j
  simp only [Hn0, decide_false]
  tp_pures j
  wp_pures
  iexists _
  iframe Hspec
  dsimp only [interp, lrel_unit]
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Rocq: `prog_eq_unit`. -/
theorem prog_eq_unit :
    (∅ : varmap type) ⊨ prog =ctx= cpl(#()) : TUnit :=
  ⟨prog_refines_unit, unit_refines_prog⟩

end Foxtrot.Examples.NodetExample
