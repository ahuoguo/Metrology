module

public import Metrology.Coneris.Examples.ParallelAddPart2

/-!
# Parallel additions of coin flips (part 3)

Ported from clutch/theories/coneris/examples/parallel_add.v (section `attempt1`:
`parallel_add_spec'`, "this time we use the property of flip being logically atomic")

See `ParallelAdd` for the Rocq → Lean map.

## Proofs that differ from Rocq
* The error function `λ x b, match excluded_middle_informative (1/2 <= x) with ...` is the
  helper `flip_adv_err` (a classical `if`); its side condition is `flip_adv_err_mean`, and its
  values in the proof are `flip_adv_err_true`/`flip_adv_err_false`.
* `wp_bind (flipL _)` is `rw [subst_flip]; wp_bind flip` (the helper `subst_flip` says `flip` is
  closed). `awp_apply (awp_flip_adv _ ..)` is at `E := ∅`; `iAaccIntro with "Herr"` is done by
  hand as in `Coneris.Examples.Race`: `iinv` without closing name, `iunfold atomic_acc`, the
  laters stripped with `imod`, `fupd_mask_intro`, the telescope instantiated with `⟨err, ⟨⟩⟩`
  and simplified with `tele_simp`.
* The Rocq `case_match eqn:Heqn; last first` (showing `1/2 <= err`) is folded into
  `flip_adv_err_true`/`flip_adv_err_false`.

## Added
`subst_flip`, `flip_adv_err`, `flip_adv_err_mean`, `flip_adv_err_true`, `flip_adv_err_false`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par Coneris.Lib.Flip Coneris.Lib.Conversion
open Coneris.Lib.HocapRandAtomic
open Iris.ExclAuth

namespace Coneris.Examples.ParallelAdd

attribute [local instance] Classical.propDecidable

/-- Helper: `flip` is closed. -/
theorem subst_flip (x : String) (v : val) : subst x v Coneris.Lib.Flip.flip =
    Coneris.Lib.Flip.flip := rfl

/-- Helper: the error function passed to `awp_flip_adv` in `parallel_add_spec'` (Rocq: an
anonymous `λ x b, match excluded_middle_informative (1/2 <= x) with ...`). -/
def flip_adv_err (x : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if 1 / 2 ≤ x then (if b then 2 * x - 1 else 1) else x

/-- Helper: the side condition of `awp_flip_adv` for `flip_adv_err` (Rocq: `intros;
case_match; simpl; lra`). -/
theorem flip_adv_err_mean (x : ℝ≥0∞) :
    x = 1 / 2 * (flip_adv_err x true + flip_adv_err x false) := by
  unfold flip_adv_err
  by_cases h : 1 / 2 ≤ x
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    have h1 : 1 ≤ 2 * x := by
      calc (1 : ℝ≥0∞) = 2 * (1 / 2) := by rw [one_div, ENNReal.mul_inv_cancel (by simp) (by simp)]
        _ ≤ 2 * x := mul_le_mul_right h 2
    rw [tsub_add_cancel_of_le h1, ← mul_assoc, one_div, ENNReal.inv_mul_cancel (by simp) (by simp),
      one_mul]
  · simp only [h, ↓reduceIte]
    rw [← two_mul, ← mul_assoc, one_div, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

/-- Helper: in `parallel_add_spec'` the flip happens while the invariant's error is
`1 - Rpower 2 (bool_to_nat b - 2) ≥ 1/2`, and afterwards the error is
`2 * (..) - 1 = 1 - Rpower 2 (bool_to_nat b - 1)`. -/
theorem flip_adv_err_true (b : Bool) :
    flip_adv_err (1 - 2 ^ (((bool_to_nat b : ℕ) : ℝ) - 2)) true =
      1 - 2 ^ ((bool_to_nat b : ℝ) - 1) := by
  rw [flip_err_rem]
  cases b
  · simp only [bool_to_nat, Bool.false_eq_true, ↓reduceIte, flip_err_zero, flip_adv_err]
    rw [ite_eq_left (by
      rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
      norm_num)]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
      ENNReal.toReal_sub_of_le (by
        rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
        simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
          ENNReal.toReal_ofNat]
        norm_num) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
      ENNReal.toReal_inv]
    norm_num
  · simp only [bool_to_nat, ↓reduceIte, flip_err_one, flip_adv_err]
    rw [ite_eq_left (by rw [one_div]), ENNReal.mul_inv_cancel (by simp) (by simp), tsub_self]

/-- Helper: see `flip_adv_err_true`. -/
theorem flip_adv_err_false (b : Bool) :
    flip_adv_err (1 - 2 ^ (((bool_to_nat b : ℕ) : ℝ) - 2)) false = 1 := by
  unfold flip_adv_err
  rw [ite_eq_left, ite_eq_right Bool.false_ne_true]
  cases b
  · simp only [bool_to_nat, Bool.false_eq_true, ↓reduceIte, flip_err_zero]
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num
  · simp only [bool_to_nat, ↓reduceIte, flip_err_one, one_div, le_refl]

section attempt1

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]
  [ElemG GF (excl_authF (Option Bool))]

/-- Rocq: `parallel_add_spec'`. This time we use the property of flip being logically
atomic. -/
theorem parallel_add_spec' :
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
  · wp_pures
    rw [subst_flip]
    wp_bind Coneris.Lib.Flip.flip
    awp_apply awp_flip_adv ∅ flip_adv_err flip_adv_err_mean
    iinv I with ⟨%b1, %b2, %fn, %err, %z, Hγ1a, Hγ2a, Hl, Herr, H, Hfn, Hz⟩
    iunfold atomic_acc
    imod Hγ1a; imod Hγ2a; imod Hl; imod Herr; imod H with %H; imod Hfn with %Hfn
    imod Hz with %Hz
    ihave %Heq := ghost_var_agree' $$ Hγ1a Hγ1f
    subst Heq Hfn Hz
    iapply fupd_mask_intro (by exact LawfulSet.empty_subset)
    iintro Hclose
    iexists ⟨err, ⟨⟩⟩
    tele_simp
    iframe Herr
    isplit
    · iintro Herr
      imod Hclose
      imodintro
      iframe Hγ1f
      inext
      iexists none, b2, _, err, _
      iframe
      ipureintro
      exact ⟨H, rfl, rfl⟩
    · iintro %b Herr
      imod Hclose
      have H' : err = 1 - 2 ^ (((bool_to_nat b2.isSome : ℕ) : ℝ) - 2) := by
        rw [H]; simp [bool_to_nat]
      rw [H']
      cases b
      · rw [flip_adv_err_false]
        iexfalso
        iapply ErrorCredit.contradict le_rfl $$ Herr
      rw [flip_adv_err_true]
      imod ghost_var_update' γ1 (some false) _ _ $$ Hγ1a Hγ1f with ⟨Hγ1a, Hγ1f⟩
      imodintro
      isplitl [Herr Hl Hγ1a Hγ2a]
      · inext
        iexists some false, b2, 1 + bool_to_nat b2.isSome, _,
          bool_to_Z (is_Some_true none) + bool_to_Z (is_Some_true b2)
        iframe
        ipureintro
        refine ⟨?_, rfl, rfl⟩
        rw [Nat.add_comm, flip_err_succ]
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
  · wp_pures
    rw [subst_flip]
    wp_bind Coneris.Lib.Flip.flip
    awp_apply awp_flip_adv ∅ flip_adv_err flip_adv_err_mean
    iinv I with ⟨%b1, %b2, %fn, %err, %z, Hγ1a, Hγ2a, Hl, Herr, H, Hfn, Hz⟩
    iunfold atomic_acc
    imod Hγ1a; imod Hγ2a; imod Hl; imod Herr; imod H with %H; imod Hfn with %Hfn
    imod Hz with %Hz
    ihave %Heq := ghost_var_agree' $$ Hγ2a Hγ2f
    subst Heq Hfn Hz
    iapply fupd_mask_intro (by exact LawfulSet.empty_subset)
    iintro Hclose
    iexists ⟨err, ⟨⟩⟩
    tele_simp
    iframe Herr
    isplit
    · iintro Herr
      imod Hclose
      imodintro
      iframe Hγ2f
      inext
      iexists b1, none, _, err, _
      iframe
      ipureintro
      exact ⟨H, rfl, rfl⟩
    · iintro %b Herr
      imod Hclose
      have H' : err = 1 - 2 ^ (((bool_to_nat b1.isSome : ℕ) : ℝ) - 2) := by
        rw [H]; simp [bool_to_nat]
      rw [H']
      cases b
      · rw [flip_adv_err_false]
        iexfalso
        iapply ErrorCredit.contradict le_rfl $$ Herr
      rw [flip_adv_err_true]
      imod ghost_var_update' γ2 (some false) _ _ $$ Hγ2a Hγ2f with ⟨Hγ2a, Hγ2f⟩
      imodintro
      isplitl [Herr Hl Hγ1a Hγ2a]
      · inext
        iexists b1, some false, bool_to_nat b1.isSome + 1, _,
          bool_to_Z (is_Some_true b1) + bool_to_Z (is_Some_true none)
        iframe
        ipureintro
        refine ⟨?_, rfl, rfl⟩
        rw [flip_err_succ]
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
