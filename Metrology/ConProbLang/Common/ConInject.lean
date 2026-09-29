module

public import Metrology.ConProbLang.Notation

/-!
# Injections into `con_prob_lang` values

Ported from clutch/theories/common/con_inject.v

## Rocq → Lean
* `Class Inject A B := { inject : A → B; inject_inj : Inj (=) (=) inject }` is the class
  `Inject A B` with fields `inject` and `inject_inj : Function.Injective inject`.
  (The Rocq `Existing Instance inject_inj` has no counterpart: `Function.Injective` is not a
  class in Lean; use `Inject.inject_inj` directly.)
* The unnamed Rocq instances get the names `Inject_int`, `Inject_nat`, `Inject_bool`,
  `Inject_unit`, `Inject_loc`, `Inject_val`.
* `SOMEV`/`NONEV`/`#()` are unfolded to `InjRV`/`InjLV (LitV LitUnit)`/`LitV LitUnit`
  (they are `abbrev`s of those in `Notation.lean`).

## Omissions
* The notation `$ x` for `inject x` (Rocq level 8) is not provided: `$` is Lean's
  application operator. Write `inject x`.
-/

@[expose] public section

namespace ConProbLang

namespace con_prob_lang

/-- Rocq: `Inject`. -/
class Inject (A B : Type) where
  inject : A → B
  inject_inj : Function.Injective inject

export Inject (inject)

/-- Rocq: `Inject_option`. -/
instance Inject_option {T : Type} [Inject T val] : Inject (Option T) val where
  inject o := match o with
    | some t => SOMEV (inject t)
    | none => NONEV
  inject_inj := by
    intro a b h
    cases a <;> cases b <;> simp_all [Inject.inject_inj.eq_iff]

/-- Rocq: `Inject_prod`. -/
instance Inject_prod {A B : Type} [Inject A val] [Inject B val] : Inject (A × B) val where
  inject p := PairV (inject p.1) (inject p.2)
  inject_inj := by
    rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    simp_all [Inject.inject_inj.eq_iff]

/-- Rocq: `Inject_sum`. -/
instance Inject_sum {A B : Type} [Inject A val] [Inject B val] : Inject (A ⊕ B) val where
  inject s := match s with
    | .inl v => InjLV (inject v)
    | .inr v => InjRV (inject v)
  inject_inj := by
    intro a b h
    cases a <;> cases b <;> simp_all [Inject.inject_inj.eq_iff]

/-- Rocq: `Inject Z val` (unnamed instance). -/
instance Inject_int : Inject ℤ val where
  inject n := LitV (LitInt n)
  inject_inj := by intro a b h; simpa using h

/-- Rocq: `Inject nat val` (unnamed instance). -/
instance Inject_nat : Inject ℕ val where
  inject n := inject (n : ℤ)
  inject_inj := by
    intro a b h
    exact Int.ofNat_inj.mp (Inject_int.inject_inj h)

/-- Rocq: `Inject bool val` (unnamed instance). -/
instance Inject_bool : Inject Bool val where
  inject b := LitV (LitBool b)
  inject_inj := by intro a b h; simpa using h

/-- Rocq: `Inject unit val` (unnamed instance). -/
instance Inject_unit : Inject Unit val where
  inject _ := LitV LitUnit
  inject_inj := by intro a b _; rfl

/-- Rocq: `Inject loc val` (unnamed instance). -/
instance Inject_loc : Inject Loc val where
  inject l := LitV (LitLoc l)
  inject_inj := by intro a b h; simpa using h

/-- Rocq: `Inject_expr`. -/
instance Inject_expr {A : Type} [Inject A val] : Inject A expr where
  inject a := Val (inject a)
  inject_inj := by
    intro a b h
    exact Inject.inject_inj (B := val) (expr.Val.inj h)

/-- Rocq: `Inject val val` (unnamed instance). -/
instance Inject_val : Inject val val where
  inject v := v
  inject_inj := fun _ _ h => h

end con_prob_lang

end ConProbLang
