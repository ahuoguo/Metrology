module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Extensions of the standard library (partial)

Ported from clutch/theories/prelude/stdpp_ext.v

This is a *partial* port: only the `fin 2` / `bool` conversions needed by the discrete
probability library (`Rcoupl_fair_coin_dunifP` in `Metrology.Prob.Couplings`) are here so far.
A full port of `prelude/stdpp_ext.v` should extend this file (and keep these names) rather than
redefine them elsewhere.

`Inj (=) (=) bool_to_fin` / `Surj (=) bool_to_fin` become `Function.Injective bool_to_fin` /
`Function.Surjective bool_to_fin`.
-/

@[expose] public section

namespace Prob

/-- Rocq: `fin_to_bool`. -/
def fin_to_bool (n : Fin 2) : Bool := decide (n ≠ 0)

/-- Rocq: `bool_to_fin`. -/
def bool_to_fin (b : Bool) : Fin 2 := if b then 1 else 0

/-- Rocq: `bool_to_fin_to_bool`. -/
@[simp] theorem bool_to_fin_to_bool (b : Bool) : fin_to_bool (bool_to_fin b) = b := by
  cases b <;> decide

/-- Rocq: `fin_to_bool_to_fin`. -/
@[simp] theorem fin_to_bool_to_fin (n : Fin 2) : bool_to_fin (fin_to_bool n) = n := by
  revert n; decide

/-- Rocq: `bool_to_fin_inj`. -/
theorem bool_to_fin_inj : Function.Injective bool_to_fin := fun a b h => by
  simpa using congrArg fin_to_bool h

/-- Rocq: `bool_to_fin_surj`. -/
theorem bool_to_fin_surj : Function.Surjective bool_to_fin := fun n =>
  ⟨fin_to_bool n, fin_to_bool_to_fin n⟩

end Prob
