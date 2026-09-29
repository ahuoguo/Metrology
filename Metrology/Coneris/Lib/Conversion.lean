module

public import Metrology.Coneris.ProofMode

/-!
# Conversions between booleans and integers

Ported from clutch/theories/coneris/lib/conversion.v

## Rocq → Lean mapping
* `bool_to_int`, `int_to_bool`, `wp_bool_to_int`, `wp_int_to_bool`: same names.
* `Z.b2z b` is `b.toInt` (Lean core `Bool.toInt`: `1` for `true`, `0` for `false`).
* `Z_to_bool` (from `clutch/prelude/stdpp_ext.v`) and its lemmas `Z_to_bool_eq_0`,
  `Z_to_bool_neq_0` are local helpers here (they are not in the Lean core files).
* Rocq's `{{{ True }}} e @ E {{{ RET v; True }}}` is iris-lean's Texan triple
  `{{ True }} (e) @ s; E {{ RET v; True }}` (the stuckness `s` is generalised; Rocq fixes it to
  `NotStuck` through the notation).
* The Rocq proofs do `case_bool_decide` on the value comparison; here we case split on `b`,
  resp. on `z = 0`, and let `wp_pures` decide the (concrete) comparison.
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.Conversion

/-! ## `Z_to_bool` (Rocq: `clutch/prelude/stdpp_ext.v`) -/

/-- Rocq: `Z_to_bool`. We take `0` to mean `false` and any other value to be `true`. -/
def Z_to_bool (z : ℤ) : Bool := if z = 0 then false else true

/-- Rocq: `Z_to_bool_eq_0`. -/
theorem Z_to_bool_eq_0 : Z_to_bool 0 = false := rfl

/-- Rocq: `Z_to_bool_neq_0`. -/
theorem Z_to_bool_neq_0 (z : ℤ) (h : z ≠ 0) : Z_to_bool z = true := by
  simp [Z_to_bool, h]

/-! ## Programs -/

/-- Rocq: `bool_to_int`. -/
def bool_to_int : val := cpl_val(
  λ b,
    if b = #false then
      #0
    else #1)

/-- Rocq: `int_to_bool`. -/
def int_to_bool : val := cpl_val(
  λ z,
    if z = #0 then #false
    else #true)

section specs

variable {GF : BundledGFunctors} [conerisGS GF] {s : Stuckness}

/-- Rocq: `wp_bool_to_int`. -/
theorem wp_bool_to_int (b : Bool) (E : CoPset) :
    {{ True }} (cpl(&bool_to_int #b)) @ s; E
    {{ RET LitV (LitInt b.toInt); (True : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold bool_to_int
  cases b
  · wp_pures
    rw [show Bool.toInt false = 0 from rfl]
    iapply HΦ $$ []
    itrivial
  · wp_pures
    rw [show Bool.toInt true = 1 from rfl]
    iapply HΦ $$ []
    itrivial

/-- Rocq: `wp_int_to_bool`. -/
theorem wp_int_to_bool (z : ℤ) (E : CoPset) :
    {{ True }} (cpl(&int_to_bool #z)) @ s; E
    {{ RET LitV (LitBool (Z_to_bool z)); (True : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold int_to_bool
  by_cases Heq : z = 0
  · subst Heq
    wp_pures
    rw [Z_to_bool_eq_0]
    iapply HΦ $$ []
    itrivial
  · wp_pures
    rw [decide_eq_false Heq]
    wp_pures
    rw [Z_to_bool_neq_0 z Heq]
    iapply HΦ $$ []
    itrivial

end specs

end Coneris.Lib.Conversion
