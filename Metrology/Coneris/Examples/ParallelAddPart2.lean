module

public import Metrology.Coneris.Examples.ParallelAdd

/-!
# Parallel additions of coin flips (part 2)

Ported from clutch/theories/coneris/examples/parallel_add.v (section `parallel_add`: the
programs `half_FAA`, `parallel_add`, `is_Some_true`, and section `attempt1` up to
`parallel_add_spec`; `parallel_add_spec'` is in `ParallelAddPart3`)

See `ParallelAdd` for the Rocq → Lean map.

## Proofs that differ from Rocq
* The `Rpower`/`lra` computations are the helpers `two_rpow_neg_one`, `two_rpow_neg_two`,
  `one_sub_half`, `one_sub_quarter`, `flip_err_zero`, `flip_err_one`, `flip_err_two`,
  `flip_err_rem`, `flip_err_mean`, `flip_err_succ` (the Rocq `mknonnegreal`/`Unshelve`
  side goals vanish).
* `rewrite /flipL; wp_pures` is `unfold flip flipL; wp_pures; wp_lam` (the call of the closure
  `flipL` is not reduced by `wp_pures` here). `inv_fin n` is a `by_cases` on the sample and
  `Fin.ext`. After `wp_int_to_bool`, `Z_to_bool 1` is rewritten to `true` before `wp_pures`.
* The pure invariant bookkeeping (`naive_solver`, `lia`) is `rcases .. <;> decide` / `simpa`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par Coneris.Lib.Flip Coneris.Lib.Conversion
open Iris.ExclAuth

namespace Coneris.Examples.ParallelAdd

/-! ## Section `parallel_add` -/

/-- Rocq: `half_FAA`. -/
def half_FAA (l : Loc) : expr := cpl(if &flip then faa(#l, #1) else #())

/-- Rocq: `parallel_add`. -/
def parallel_add : expr := cpl(
  let r := ref(#0) in
  ((if &flip then faa(r, #1) else #())
   ‖
   (if &flip then faa(r, #1) else #()));
  !r)

/-- Rocq: `is_Some_true`. -/
def is_Some_true : Option Bool → Bool
  | some true => true
  | _ => false

/-! ### Error arithmetic (Rocq: `Rpower` computations, `lra`) -/

/-- Helper: `Rpower 2 (-1) = 1/2`. -/
theorem two_rpow_neg_one : (2 : ℝ≥0∞) ^ (-1 : ℝ) = 2⁻¹ := ENNReal.rpow_neg_one 2

/-- Helper: `Rpower 2 (-2) = 1/4`. -/
theorem two_rpow_neg_two : (2 : ℝ≥0∞) ^ (-2 : ℝ) = 4⁻¹ := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_two]
  norm_num

/-- Helper: `1 - 1/2 = 1/2` in `ℝ≥0∞`. -/
theorem one_sub_half : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := ENNReal.one_sub_inv_two

/-- Helper: `1 - 1/4 = 3/4` in `ℝ≥0∞`. -/
theorem one_sub_quarter : (1 : ℝ≥0∞) - 4⁻¹ = 3 / 4 := by
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
    ENNReal.toReal_sub_of_le (by norm_num) (by finiteness)]
  simp only [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_div]
  norm_num

/-- Helper: the flip error `1 - 2 ^ (k - 2)` for `k = 0, 1, 2` (the truncated subtraction of
`ℝ≥0∞` agrees with Rocq's real subtraction, since `2 ^ (k - 2) ≤ 1`). -/
theorem flip_err_zero : (1 : ℝ≥0∞) - 2 ^ (((0 : ℕ) : ℝ) - 2) = 3 / 4 := by
  rw [Nat.cast_zero, zero_sub, two_rpow_neg_two, one_sub_quarter]

@[inherit_doc flip_err_zero]
theorem flip_err_one : (1 : ℝ≥0∞) - 2 ^ (((1 : ℕ) : ℝ) - 2) = 2⁻¹ := by
  rw [Nat.cast_one, show (1 : ℝ) - 2 = -1 by norm_num, two_rpow_neg_one, one_sub_half]

@[inherit_doc flip_err_zero]
theorem flip_err_two : (1 : ℝ≥0∞) - 2 ^ (((2 : ℕ) : ℝ) - 2) = 0 := by
  norm_num

/-- Helper: `1 - Rpower 2 (bool_to_nat b - 1)`, the error left for a thread after the other
thread flipped (`b`) or not. -/
theorem flip_err_rem (b : Bool) :
    (1 : ℝ≥0∞) - 2 ^ ((bool_to_nat b : ℝ) - 1) = if b then 0 else 2⁻¹ := by
  cases b
  · simp only [bool_to_nat, Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, zero_sub,
      two_rpow_neg_one, one_sub_half]
  · simp [bool_to_nat]

/-- Helper: the mean of the error function in `parallel_add_spec` (Rocq:
`SeriesC_finite_foldr; ...; Rpower_plus; lra`). -/
theorem flip_err_mean (b : Bool) :
    1 / 2 * ((1 - 2 ^ ((bool_to_nat b : ℝ) - 1)) + 1) =
      (1 : ℝ≥0∞) - 2 ^ (((bool_to_nat b : ℕ) : ℝ) - 2) := by
  rw [flip_err_rem]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, bool_to_nat, flip_err_zero]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_div, ENNReal.toReal_one]
    norm_num
  · simp only [↓reduceIte, bool_to_nat, flip_err_one, zero_add, mul_one, one_div]

/-- Helper: `1 - Rpower 2 ((S k) - 2) = 1 - Rpower 2 (k - 1)`. -/
theorem flip_err_succ (k : ℕ) :
    (1 : ℝ≥0∞) - 2 ^ (((k + 1 : ℕ) : ℝ) - 2) = 1 - 2 ^ ((k : ℝ) - 1) := by
  congr 2
  push_cast
  ring

/-! ### Section `attempt1` -/

section attempt1

/-! More complicated spec, where the error is stored in the invariant for adv comp. -/

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]
  [ElemG GF (excl_authF (Option Bool))]

/-- Rocq: `parallel_add_inv` (section `attempt1`; "Ideally err should be a R"). The Rocq
`err : nonnegreal` with `nonneg err = 1 - Rpower 2 (INR flip_num - 2)` is `err : ℝ≥0∞` with
`err = 1 - 2 ^ ((flip_num : ℝ) - 2)` (`ENNReal.rpow`; the truncated subtraction agrees with
Rocq since `flip_num ≤ 2`). -/
def parallel_add_inv (l : Loc) (γ1 γ2 : GName) : IProp GF :=
  iprop(∃ (b1 b2 : Option Bool) (flip_num : ℕ) (err : ℝ≥0∞) (z : ℤ),
    own_auth γ1 b1 ∗ own_auth γ2 b2 ∗ l ↦ LitV (LitInt z) ∗
    ↯ err ∗
    ⌜err = 1 - (2 : ℝ≥0∞) ^ ((flip_num : ℝ) - 2)⌝ ∗
    ⌜flip_num = bool_to_nat b1.isSome + bool_to_nat b2.isSome⌝ ∗
    ⌜z = bool_to_Z (is_Some_true b1) + bool_to_Z (is_Some_true b2)⌝)

/-- Rocq: `parallel_add_spec`. -/
theorem parallel_add_spec :
    {{ ↯ (3 / 4) }} parallel_add
    {{ (z : ℤ), RET LitV (LitInt z); (⌜z = 2⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold parallel_add
  wp_alloc l as Hl
  wp_pures
  imod ghost_var_alloc' none with ⟨%γ1, Hγ1a, Hγ1f⟩
  imod ghost_var_alloc' none with ⟨%γ2, Hγ2a, Hγ2f⟩
  imod inv_alloc nroot ⊤ (parallel_add_inv l γ1 γ2) $$ [Hl Hγ1a Hγ2a Herr] with #I
  · inext
    unfold parallel_add_inv
    iexists none, none, 0, 3 / 4, 0
    iframe
    ipureintro
    exact ⟨flip_err_zero.symm, rfl, rfl⟩
  unfold parallel_add_inv
  wp_apply wp_par' (fun _ => own_frag γ1 (some true)) (fun _ => own_frag γ2 (some true))
    $$ [Hγ1f] [Hγ2f]
  · unfold Coneris.Lib.Flip.flip flipL
    wp_pures
    wp_lam
    wp_bind (Rand _ _)
    iinv I with ⟨%b1, %b2, %fn, %err, %z, >Hγ1a, >Hγ2a, >Hl, >Herr, >%H, >%Hfn, >%Hz⟩ Hclose
    ihave %Heq := ghost_var_agree' $$ Hγ1a Hγ1f
    subst Heq Hfn Hz
    wp_apply wp_couple_rand_adv_comp1 1 1 err
      (fun x => if (x : ℕ) = 0 then 1 else 1 - 2 ^ ((bool_to_nat b2.isSome : ℝ) - 1)) rfl
      (by rw [flip_SeriesC_unif, H]; simpa [bool_to_nat] using flip_err_mean b2.isSome)
      $$ Herr with %n Herr
    by_cases hn : (n : ℕ) = 0
    · simp only [hn, ↓reduceIte]
      iexfalso
      iapply ErrorCredit.contradict le_rfl $$ Herr
    obtain rfl : n = 1 := Fin.ext (by have := n.isLt; simp only [Fin.val_one]; omega)
    simp only [Fin.val_one, one_ne_zero, ↓reduceIte, Nat.cast_one]
    imod ghost_var_update' γ1 (some false) _ _ $$ Hγ1a Hγ1f with ⟨Hγ1a, Hγ1f⟩
    imod Hclose $$ [Hγ1a Hγ2a Hl Herr]
    · inext
      iexists some false, b2, 1 + bool_to_nat b2.isSome, _,
        bool_to_Z (is_Some_true none) + bool_to_Z (is_Some_true b2)
      iframe
      ipureintro
      refine ⟨?_, rfl, rfl⟩
      rw [Nat.add_comm, flip_err_succ]
    imodintro
    wp_apply wp_int_to_bool $$ [] with -
    · itrivial
    rw [show Z_to_bool 1 = true from rfl]
    wp_pures
    iinv I with ⟨%b1, %b2', %fn, %err, %z, >Hγ1a, >Hγ2a, >Hl, >Herr, >%H, >%Hfn, >%Hz⟩ Hclose
    ihave %Heq := ghost_var_agree' $$ Hγ1a Hγ1f
    subst Heq
    wp_faa
    imod ghost_var_update' γ1 (some true) _ _ $$ Hγ1a Hγ1f with ⟨Hγ1a, Hγ1f⟩
    imod Hclose $$ [Hγ1a Hγ2a Hl Herr]
    · inext
      iexists some true, b2', fn, err, z + 1
      iframe
      ipureintro
      refine ⟨H, Hfn, ?_⟩
      rw [Hz]
      rcases b2' with _ | _ | _ <;> decide
    imodintro
    iexact Hγ1f
  · unfold Coneris.Lib.Flip.flip flipL
    wp_pures
    wp_lam
    wp_bind (Rand _ _)
    iinv I with ⟨%b1, %b2, %fn, %err, %z, >Hγ1a, >Hγ2a, >Hl, >Herr, >%H, >%Hfn, >%Hz⟩ Hclose
    ihave %Heq := ghost_var_agree' $$ Hγ2a Hγ2f
    subst Heq Hfn Hz
    wp_apply wp_couple_rand_adv_comp1 1 1 err
      (fun x => if (x : ℕ) = 0 then 1 else 1 - 2 ^ ((bool_to_nat b1.isSome : ℝ) - 1)) rfl
      (by rw [flip_SeriesC_unif, H]; simpa [bool_to_nat] using flip_err_mean b1.isSome)
      $$ Herr with %n Herr
    by_cases hn : (n : ℕ) = 0
    · simp only [hn, ↓reduceIte]
      iexfalso
      iapply ErrorCredit.contradict le_rfl $$ Herr
    obtain rfl : n = 1 := Fin.ext (by have := n.isLt; simp only [Fin.val_one]; omega)
    simp only [Fin.val_one, one_ne_zero, ↓reduceIte, Nat.cast_one]
    imod ghost_var_update' γ2 (some false) _ _ $$ Hγ2a Hγ2f with ⟨Hγ2a, Hγ2f⟩
    imod Hclose $$ [Hγ1a Hγ2a Hl Herr]
    · inext
      iexists b1, some false, bool_to_nat b1.isSome + 1, _,
        bool_to_Z (is_Some_true b1) + bool_to_Z (is_Some_true none)
      iframe
      ipureintro
      refine ⟨?_, rfl, rfl⟩
      rw [flip_err_succ]
    imodintro
    wp_apply wp_int_to_bool $$ [] with -
    · itrivial
    rw [show Z_to_bool 1 = true from rfl]
    wp_pures
    iinv I with ⟨%b1', %b2, %fn, %err, %z, >Hγ1a, >Hγ2a, >Hl, >Herr, >%H, >%Hfn, >%Hz⟩ Hclose
    ihave %Heq := ghost_var_agree' $$ Hγ2a Hγ2f
    subst Heq
    wp_faa
    imod ghost_var_update' γ2 (some true) _ _ $$ Hγ2a Hγ2f with ⟨Hγ2a, Hγ2f⟩
    imod Hclose $$ [Hγ1a Hγ2a Hl Herr]
    · inext
      iexists b1', some true, fn, err, z + 1
      iframe
      ipureintro
      refine ⟨H, Hfn, ?_⟩
      rw [Hz]
      rcases b1' with _ | _ | _ <;> decide
    imodintro
    iexact Hγ2f
  · iintro %v1 %v2 ⟨Hγ1f, Hγ2f⟩
    inext
    wp_pures
    iinv I with ⟨%b1, %b2, %fn, %err, %z, >Hγ1a, >Hγ2a, >Hl, >Herr, >%H, >%Hfn, >%Hz⟩ Hclose
    wp_load
    ihave %Heq1 := ghost_var_agree' $$ Hγ1a Hγ1f
    ihave %Heq2 := ghost_var_agree' $$ Hγ2a Hγ2f
    subst Heq1 Heq2
    imod Hclose $$ [Hγ1a Hγ2a Hl Herr]
    · inext
      iexists some true, some true, fn, err, z
      iframe
      ipureintro
      exact ⟨H, Hfn, Hz⟩
    imodintro
    iapply HΦ
    ipureintro
    simpa [is_Some_true, bool_to_Z] using Hz

end attempt1

end Coneris.Examples.ParallelAdd
