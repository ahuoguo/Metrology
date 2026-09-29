module

public import Metrology.Coneris.ErrorRules
public import Metrology.Coneris.Atomic
public import Metrology.Coneris.Lib.Conversion
public import Metrology.Coneris.Lib.HocapRandAtomic

/-!
# Derived laws for a fair coin flip

Ported from clutch/theories/coneris/lib/flip.v

## Rocq → Lean mapping
* `flipL`, `flip`, `allocB`, `tapeB`, `bool_tape` (notation `l ↪B bs`), `tape_conversion_bool_nat`,
  `tape_conversion_nat_bool`, `wp_allocB_tape`, `wp_flip`, `wp_flip_adv`, `awp_flip_adv`,
  `awp_flip_adv'`, `wp_flipL`, `wp_flipL_empty`, `wp_presample_bool_adv_comp`,
  `wp_presample_bool`: same names. Programs are transcribed with the `cpl` notation
  (`rand("e") #1%nat` is `rand(e) #1`, `flipL #lbl:α` is `cpl(&flipL #lbl(α))`).
* `tape` is the structure `⟨bound, contents⟩`, so `(1; bool_to_fin <$> bs)` is
  `⟨1, bs.map bool_to_fin⟩`; `bool_to_fin` is `Prob.bool_to_fin`.
* `(λ b:bool, if b then 1 else 0) <$> bs` is `bs.map (fun b => if b then 1 else 0)`;
  `(λ n, n =? 1) <$> ns` is `ns.map (fun n => n == 1)`.
* `⊣⊢` is iris-lean's `BiEntails` (`.mp`/`.mpr`).
* Errors are `ℝ≥0∞`: all hypotheses `0 <= ε2 b`, `0 <= ε` are dropped (they hold trivially).
  The equations/inequalities on `ε` are kept literally (`1/2 * (..)`, `(..)/2 <= ε1`,
  `ε >= 1/2 * (..)`); no truncated subtraction or division by zero is involved.
* Texan triples are iris-lean's `{{ P }} e @ E {{ x, RET v; Q }}` (NotStuck, as in Rocq);
  `RET #(LitBool b)` is `RET LitV (LitBool b)`, `RET #lbl:α` is `RET LitV (LitLbl α)`.
* Logically atomic triples `<<{ ∀∀ ε, ↯ ε }>> flip @ E <<{ ∃∃ b, ↯ (ε2 ε b) | RET #b }>>` use
  iris-lean's notation, elaborating to `Coneris.atomic_wp`. The telescopes are reduced with
  `tele_simp` (from `Coneris.Lib.HocapRandAtomic`).
* `wp_presample_bool_adv_comp`, `wp_presample_bool` take the WP data `E e α Φ` explicitly, as in
  Rocq, and are entailments `P ⊢ WP ..`.

## Proofs that differ from Rocq
* The Rocq `inv_fin` case splits are `fin_cases`; the sums over `fin 2`
  (`SeriesC_finite_foldr`) are the helper `flip_SeriesC_unif`.
* In `wp_flip_adv`/`awp_flip_adv(')`, the error function after `int_to_bool` is rewritten with
  the helper `flip_err_eq` instead of case-splitting on the sample (`inv_fin n`); in the atomic
  versions the atomic update is committed with `b := Z_to_bool n`.

## Added helpers (not in this Rocq file)
* `nat_to_bool`, `nat_to_bool_eq_0`, `nat_to_bool_neq_0`, `bool_to_nat`, `Z_to_bool_of_nat`
  (Rocq: `clutch/prelude/stdpp_ext.v`, not in the Lean core files).
* `bool_tape_timeless` (Rocq infers it), `tapeB_map_val`, `flip_SeriesC_unif`, `flip_err_eq`.

## Omitted
* `Global Opaque tapeB`: Rocq-specific conversion control (`tapeB` is a plain `def`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris.Lib.Conversion Coneris.Lib.HocapRandAtomic

namespace Coneris.Lib.Flip

/-! ## Helpers from `clutch/prelude/stdpp_ext.v` -/

/-- Rocq: `nat_to_bool` (from `clutch/prelude/stdpp_ext.v`). -/
def nat_to_bool (n : ℕ) : Bool := if n = 0 then false else true

/-- Rocq: `nat_to_bool_eq_0`. -/
theorem nat_to_bool_eq_0 : nat_to_bool 0 = false := rfl

/-- Rocq: `nat_to_bool_neq_0`. -/
theorem nat_to_bool_neq_0 (n : ℕ) (h : n ≠ 0) : nat_to_bool n = true := by
  simp [nat_to_bool, h]

/-- Rocq: `bool_to_nat` (from `clutch/prelude/stdpp_ext.v`). -/
def bool_to_nat (b : Bool) : ℕ := if b then 1 else 0

/-- Rocq: `Z_to_bool_of_nat`. -/
theorem Z_to_bool_of_nat (n : ℕ) : Z_to_bool (n : ℤ) = nat_to_bool n := by
  cases n
  · rfl
  · simp [Z_to_bool, nat_to_bool]; omega

/-! ## Programs -/

/-- Rocq: `flipL`. -/
def flipL : val := cpl_val(λ e, &int_to_bool (rand(e) #1))

/-- Rocq: `flip`. -/
def flip : expr := cpl(&flipL #())

/-- Rocq: `allocB`. -/
def allocB : expr := cpl(alloc(#1))

/-- Rocq: `tapeB`. -/
def tapeB (bs : List Bool) : tape := ⟨1, bs.map bool_to_fin⟩

/-- Rocq: `bool_tape`. -/
def bool_tape {GF : BundledGFunctors} [conerisGS GF] (l : Loc) (bs : List Bool) : IProp GF :=
  iprop(l ↪ tapeB bs)

/-- Rocq: `l ↪B bs`. -/
notation:50 l:50 " ↪B " bs:50 => bool_tape l bs

/-- Helper (Rocq infers it by unfolding). -/
instance bool_tape_timeless {GF : BundledGFunctors} [conerisGS GF] (l : Loc) (bs : List Bool) :
    Timeless (l ↪B bs) := by
  unfold bool_tape; infer_instance

section specs

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Helper: the tape `tapeB bs` read as natural numbers. -/
theorem tapeB_map_val (bs : List Bool) :
    (bs.map bool_to_fin).map (fun x : Fin 2 => (x : ℕ)) = bs.map (fun b => if b then 1 else 0) := by
  simp only [List.map_map]
  congr 1
  funext b
  cases b <;> rfl

/-- Rocq: `tape_conversion_bool_nat`. -/
theorem tape_conversion_bool_nat (α : Loc) (bs : List Bool) :
    α ↪B bs ⊣⊢@{IProp GF} α ↪N (1; bs.map (fun b => if b then 1 else 0)) := by
  unfold bool_tape nat_tape tapeB
  constructor
  · iintro H
    iexists bs.map bool_to_fin
    iframe H
    ipureintro
    exact tapeB_map_val bs
  · iintro ⟨%fs, %Hfs, H⟩
    have : fs = bs.map bool_to_fin :=
      List.map_injective_iff.2 Fin.val_injective (Hfs.trans (tapeB_map_val bs).symm)
    subst this
    iexact H

/-- Rocq: `tape_conversion_nat_bool`. -/
theorem tape_conversion_nat_bool (α : Loc) (ns : List ℕ) :
    α ↪N (1; ns) ⊢@{IProp GF} α ↪B (ns.map (fun n => n == 1)) := by
  unfold bool_tape nat_tape tapeB
  iintro ⟨%fs, %Hfs, H⟩
  subst Hfs
  have : ((fs.map (fun x : Fin 2 => (x : ℕ))).map (fun n => n == 1)).map bool_to_fin = fs := by
    simp only [List.map_map]
    conv => rhs; rw [← List.map_id fs]
    congr 1
    funext x
    fin_cases x <;> rfl
  rw [this]
  iexact H

/-- Rocq: `wp_allocB_tape`. -/
theorem wp_allocB_tape (E : CoPset) :
    {{ True }} allocB @ E {{ α, RET LitV (LitLbl α); (α ↪B [] : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold allocB
  wp_apply wp_alloc_tape 1 1 rfl $$ [] with %α Hα
  · itrivial
  iapply HΦ
  have h : α ↪N (1; []) ⊢@{IProp GF} α ↪B [] := tape_conversion_nat_bool α []
  iapply h $$ Hα

/-- Rocq: `wp_flip`. -/
theorem wp_flip (E : CoPset) :
    {{ True }} flip @ E {{ (b : Bool), RET LitV (LitBool b); (True : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold flip flipL
  wp_pures
  wp_bind (Rand _ _)
  wp_apply wp_rand 1 1 rfl $$ [] with %n -
  · itrivial
  wp_apply wp_int_to_bool $$ [] with -
  · itrivial
  iapply HΦ
  itrivial


/-- Helper: the uniform average over `Fin 2`. -/
theorem flip_SeriesC_unif (f : Fin 2 → ℝ≥0∞) :
    ∑' x : Fin 2, 1 / (((1 : ℕ) : ℝ≥0∞) + 1) * f x = 1 / 2 * (f 1 + f 0) := by
  rw [tsum_fintype, Fin.sum_univ_two, ← mul_add, add_comm (f 0)]
  norm_num

/-- Helper: the error function of `wp_flip_adv`, read off the result of `int_to_bool`. -/
theorem flip_err_eq (ε2 : Bool → ℝ≥0∞) (n : Fin 2) :
    (if (n : ℕ) = 0 then ε2 false else ε2 true) = ε2 (Z_to_bool ((n : ℕ) : ℤ)) := by
  fin_cases n <;> rfl

/-- Rocq: `wp_flip_adv`. -/
theorem wp_flip_adv (E : CoPset) (ε : ℝ≥0∞) (ε2 : Bool → ℝ≥0∞)
    (hε : ε = 1 / 2 * (ε2 true + ε2 false)) :
    {{ ↯ ε }} flip @ E {{ (b : Bool), RET LitV (LitBool b); (↯ (ε2 b) : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold flip flipL
  wp_pures
  wp_bind (Rand _ _)
  wp_apply wp_couple_rand_adv_comp1 1 1 ε (fun x => if (x : ℕ) = 0 then ε2 false else ε2 true)
    rfl (by rw [flip_SeriesC_unif, hε]; rfl) $$ Herr with %n Herr
  wp_apply wp_int_to_bool $$ [] with -
  · itrivial
  iapply HΦ
  iapply ErrorCredit.ext (flip_err_eq ε2 n) $$ Herr

/-- Rocq: `awp_flip_adv`. -/
theorem awp_flip_adv (E : CoPset) (ε2 : ℝ≥0∞ → Bool → ℝ≥0∞)
    (K : ∀ ε, ε = 1 / 2 * (ε2 ε true + ε2 ε false)) :
    ⊢@{IProp GF} iprop(<<{ ∀∀ (ε : ℝ≥0∞), ↯ ε }>> flip @ E
      <<{ ∃∃ (b : Bool), ↯ (ε2 ε b) | RET LitV (LitBool b) }>>) := by
  iunfold atomic_wp
  iintro %Φ AU
  unfold flip flipL
  wp_pures
  wp_bind (Rand _ _)
  imod AU with ⟨%⟨ε, ⟨⟩⟩, Herr, -, Hclose⟩
  tele_simp
  wp_apply wp_couple_rand_adv_comp1 1 1 ε
    (fun x => if (x : ℕ) = 0 then ε2 ε false else ε2 ε true)
    rfl (by rw [flip_SeriesC_unif]; exact (K ε).symm) $$ Herr with %n Herr
  imod Hclose $$ %(Z_to_bool ((n : ℕ) : ℤ)) [Herr] with HΦ
  · iapply ErrorCredit.ext (flip_err_eq (ε2 ε) n) $$ Herr
  imodintro
  wp_apply wp_int_to_bool $$ [] with -
  · itrivial
  iexact HΦ

/-- Rocq: `awp_flip_adv'`. -/
theorem awp_flip_adv' (E : CoPset) (ε2 : ℝ≥0∞ → Bool → ℝ≥0∞)
    (K : ∀ ε, ε ≥ 1 / 2 * (ε2 ε true + ε2 ε false)) :
    ⊢@{IProp GF} iprop(<<{ ∀∀ (ε : ℝ≥0∞), ↯ ε }>> flip @ E
      <<{ ∃∃ (b : Bool), ↯ (ε2 ε b) | RET LitV (LitBool b) }>>) := by
  iunfold atomic_wp
  iintro %Φ AU
  unfold flip flipL
  wp_pures
  wp_bind (Rand _ _)
  imod AU with ⟨%⟨ε, ⟨⟩⟩, Herr, -, Hclose⟩
  tele_simp
  wp_apply wp_couple_rand_adv_comp1' 1 1 ε
    (fun x => if (x : ℕ) = 0 then ε2 ε false else ε2 ε true)
    rfl (by rw [flip_SeriesC_unif]; exact K ε) $$ Herr with %n Herr
  imod Hclose $$ %(Z_to_bool ((n : ℕ) : ℤ)) [Herr] with HΦ
  · iapply ErrorCredit.ext (flip_err_eq (ε2 ε) n) $$ Herr
  imodintro
  wp_apply wp_int_to_bool $$ [] with -
  · itrivial
  iexact HΦ

/-- Rocq: `wp_flipL`. -/
theorem wp_flipL (E : CoPset) (α : Loc) (b : Bool) (bs : List Bool) :
    {{ ▷ α ↪B (b :: bs) }} cpl(&flipL #lbl(α)) @ E
    {{ RET LitV (LitBool b); (α ↪B bs : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  unfold flipL
  wp_pures
  wp_bind (Rand _ _)
  ihave Hl := (tape_conversion_bool_nat α (b :: bs)).mp $$ Hl
  simp only [List.map_cons]
  wp_apply wp_rand_tape 1 α _ _ 1 rfl $$ Hl with ⟨Hl, -⟩
  wp_apply wp_int_to_bool $$ [] with -
  · itrivial
  have hb : Z_to_bool (((if b then 1 else 0 : ℕ)) : ℤ) = b := by
    cases b <;> rfl
  rw [hb]
  iapply HΦ
  iapply (tape_conversion_bool_nat α bs).mpr $$ Hl

/-- Rocq: `wp_flipL_empty`. -/
theorem wp_flipL_empty (E : CoPset) (α : Loc) :
    {{ ▷ α ↪B [] }} cpl(&flipL #lbl(α)) @ E
    {{ (b : Bool), RET LitV (LitBool b); (α ↪B [] : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  unfold flipL
  wp_pures
  wp_bind (Rand _ _)
  have h0 : α ↪B [] ⊢@{IProp GF} α ↪N (1; []) := (tape_conversion_bool_nat α []).mp
  ihave Hl := h0 $$ Hl
  wp_apply wp_rand_tape_empty 1 1 α rfl $$ Hl with %n ⟨Hl, -⟩
  wp_apply wp_int_to_bool $$ [] with -
  · itrivial
  iapply HΦ
  have h : α ↪N (1; []) ⊢@{IProp GF} α ↪B [] := tape_conversion_nat_bool α []
  iapply h $$ Hl

/-- Rocq: `wp_presample_bool_adv_comp`. -/
theorem wp_presample_bool_adv_comp (E : CoPset) (e : expr) (α : Loc) (Φ : val → IProp GF)
    (bs : List Bool) (ε1 : ℝ≥0∞) (ε2 : Bool → ℝ≥0∞) (Hineq : (ε2 true + ε2 false) / 2 ≤ ε1) :
    ▷ α ↪B bs ∗ ↯ ε1 ∗ (∀ b, ↯ (ε2 b) ∗ α ↪B (bs ++ [b]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }} := by
  iintro ⟨>Hα, Herr, HΦ⟩
  ihave Hα := (tape_conversion_bool_nat α bs).mp $$ Hα
  iapply wp_presample_adv_comp 1 α _ ε1 (fun x => ε2 ((x : ℕ) == 1))
    (by rw [flip_SeriesC_unif, one_div, ← ENNReal.div_eq_inv_mul]; exact Hineq)
  isplitl [Hα]
  · inext
    iexact Hα
  isplitl [Herr]
  · iexact Herr
  iintro %n ⟨Herr, Hα⟩
  iapply HΦ $$ %((n : ℕ) == 1)
  iframe Herr
  iapply (tape_conversion_bool_nat α _).mpr
  have hn : (bs ++ [(n : ℕ) == 1]).map (fun b => if b then 1 else 0) =
      bs.map (fun b => if b then 1 else 0) ++ [(n : ℕ)] := by
    rw [List.map_append]
    fin_cases n <;> rfl
  rw [hn]
  iexact Hα

/-- Rocq: `wp_presample_bool`. -/
theorem wp_presample_bool (E : CoPset) (e : expr) (α : Loc) (Φ : val → IProp GF)
    (bs : List Bool) :
    ▷ α ↪B bs ∗ (∀ b, α ↪B (bs ++ [b]) -∗ WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }} := by
  iintro ⟨>Hα, HΦ⟩
  ihave Hα := (tape_conversion_bool_nat α bs).mp $$ Hα
  iapply wp_presample 1 α _
  isplitl [Hα]
  · inext
    iexact Hα
  iintro %n Hα
  ihave %Hlt := tapeN_ineq α 1 _ $$ Hα
  iapply HΦ $$ %(n == 1)
  iapply (tape_conversion_bool_nat α _).mpr
  have hn : (bs ++ [n == 1]).map (fun b => if b then 1 else 0) =
      bs.map (fun b => if b then 1 else 0) ++ [n] := by
    have : n ≤ 1 := Hlt n (List.mem_append_right _ (List.mem_singleton_self n))
    rw [List.map_append]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with rfl | rfl <;> rfl
  rw [hn]
  iexact Hα

end specs

end Coneris.Lib.Flip
