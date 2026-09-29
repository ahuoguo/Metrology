module

public import Metrology.Foxtrot.SpecProofMode

/-!
# Conversions between booleans and integers

Ported from clutch/theories/foxtrot/lib/conversion.v

## Rocq → Lean map
* `bool_to_int`, `int_to_bool`, `wp_bool_to_int`, `spec_bool_to_int`, `wp_int_to_bool`,
  `spec_int_to_bool`: same names.
* `Z.b2z b` is `b.toInt` (Lean core `Bool.toInt`, `1` for `true`, `0` for `false`).
* `Z_to_bool` (from `clutch/prelude/stdpp_ext.v`) and its lemmas `Z_to_bool_eq_0`,
  `Z_to_bool_neq_0` are local helpers here (they are not in the Lean core files).

## Deviations
* Rocq's `{{{ True }}} e @ E {{{ RET v; True }}}` is iris-lean's Texan triple
  `{{ True }} (e) @ s; E {{ RET v; True }}` (with a stuckness `s`, ignored by the Foxtrot WP).
* Rocq's `j ⤇ fill K e -∗ pupd E E (..)` is the entailment `j ⤇ fill K e ⊢ pupd E E (..)`.
* The Rocq proofs do `case_bool_decide` on the value comparison; here the proofs split on `b`
  (then `wp_pures`/`tp_pures` decide the concrete comparison), resp. on `z = 0` (then the
  `decide (z = 0)` left by the comparison is rewritten).
* For `b = true`, a single `wp_pure`/`tp_pure j` precedes `wp_pures`/`tp_pures j`: `wp_pures`
  started on `bool_to_int #true` stops before the comparison `#true = #false` (the strict
  variant of the step does not discharge its `vals_compare_safe` side condition there), while
  the same `wp_pures` started after the β-step goes through.
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.Lib.Conversion

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

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness}

/-- Rocq: `wp_bool_to_int`. -/
theorem wp_bool_to_int (b : Bool) (E : CoPset) :
    {{ True }} (cpl(&bool_to_int #b)) @ s; E {{ RET LitV (LitInt b.toInt); (True : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold bool_to_int
  cases b
  · wp_pures
    rw [show Bool.toInt false = 0 from rfl]
    iapply HΦ $$ []
    itrivial
  · wp_pure
    wp_pures
    rw [show Bool.toInt true = 1 from rfl]
    iapply HΦ $$ []
    itrivial

/-- Rocq: `spec_bool_to_int`. -/
theorem spec_bool_to_int (E : CoPset) (j : ℕ) (K : List ectx_item) (b : Bool) :
    j ⤇ fill K cpl(&bool_to_int #b) ⊢@{IProp GF}
      pupd E E (j ⤇ fill K (Val (LitV (LitInt b.toInt)))) := by
  unfold bool_to_int
  iintro HK
  cases b
  · tp_pures j
    rw [show Bool.toInt false = 0 from rfl]
    imodintro
    iexact HK
  · tp_pure j
    tp_pures j
    rw [show Bool.toInt true = 1 from rfl]
    imodintro
    iexact HK

/-- Rocq: `wp_int_to_bool`. -/
theorem wp_int_to_bool (z : ℤ) (E : CoPset) :
    {{ True }} (cpl(&int_to_bool #z)) @ s; E
    {{ RET LitV (LitBool (Z_to_bool z)); (True : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold int_to_bool
  wp_pures
  by_cases Heq : z = 0
  · subst Heq
    rw [decide_eq_true rfl]
    wp_pures
    rw [Z_to_bool_eq_0]
    iapply HΦ $$ []
    itrivial
  · rw [decide_eq_false Heq]
    wp_pures
    rw [Z_to_bool_neq_0 z Heq]
    iapply HΦ $$ []
    itrivial

/-- Rocq: `spec_int_to_bool`. -/
theorem spec_int_to_bool (E : CoPset) (j : ℕ) (K : List ectx_item) (z : ℤ) :
    j ⤇ fill K cpl(&int_to_bool #z) ⊢@{IProp GF}
      pupd E E (j ⤇ fill K (Val (LitV (LitBool (Z_to_bool z))))) := by
  unfold int_to_bool
  iintro HK
  tp_pures j
  by_cases Heq : z = 0
  · subst Heq
    rw [decide_eq_true rfl]
    tp_pures j
    rw [Z_to_bool_eq_0]
    imodintro
    iexact HK
  · rw [decide_eq_false Heq]
    tp_pures j
    rw [Z_to_bool_neq_0 z Heq]
    imodintro
    iexact HK

end specs

end Foxtrot.Lib.Conversion
