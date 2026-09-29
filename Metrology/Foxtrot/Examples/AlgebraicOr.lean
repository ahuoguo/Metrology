module

public import Metrology.Foxtrot.Examples.Algebraic

/-!
# Algebraic theory (part 6: `or`, `eq4` … `eq8`)

Ported from clutch/theories/foxtrot/examples/algebraic.v (sections `eq4` … `eq8`).

## Rocq → Lean map
* `eq4`, `eq5`, `eq6`, `eq7`, `eq8`: same names.
* `iMod (tp_or _ _ _ b with "[$]")` is `imod tp_or j K ⊤ b _ _ $$ Hspec with Hspec` followed by
  `simp only [↓reduceIte]` (the Lean `tp_or` returns an `if b then .. else ..`).
* In `eq8`, the continuation of `wp_or` is proven first (`rotate_left`), to fix its
  postcondition before `case_bool_decide` is used on the precondition.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel Foxtrot.Lib.Toss Foxtrot.Lib.Or Foxtrot.Lib.Diverge

namespace Foxtrot.Examples.Algebraic

section eq4

/-- Rocq: `eq4`. -/
theorem eq4 (e : expr) (τ : type) (H : ∅ ⊢ₜ e : τ) : ∅ ⊨ or e e =ctx= e : τ := by
  constructor
  · apply refines_sound foxtrotSigma
    intro _ Δ
    ihave H := refines_typed τ Δ e H
    unfold_rel
    iintro %K %j Hspec
    wp_apply wp_or e e _ $$ [-]
    · isplit
      · iapply H $$ Hspec
      · iapply H $$ Hspec
    · iintro %v Hv
      iexact Hv
  · apply refines_sound foxtrotSigma
    intro _ Δ
    ihave H := refines_typed τ Δ e H
    unfold_rel
    iintro %K %j Hspec
    imod tp_or j K ⊤ true e e $$ Hspec with Hspec
    simp only [↓reduceIte]
    iapply H $$ Hspec

end eq4

section eq5

/-- Rocq: `eq5`. -/
theorem eq5 (e1 e2 : expr) (τ : type) (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) :
    ∅ ⊨ or e1 e2 =ctx= or e2 e1 : τ := by
  constructor
  · apply refines_sound foxtrotSigma
    intro _ Δ
    ihave H1 := refines_typed τ Δ e1 H1
    ihave H2 := refines_typed τ Δ e2 H2
    unfold_rel
    iintro %K %j Hspec
    wp_apply wp_or e1 e2 _ $$ [-]
    · isplit
      · imod tp_or j K ⊤ false e2 e1 $$ Hspec with Hspec
        simp only [Bool.false_eq_true, ↓reduceIte]
        iapply H1 $$ Hspec
      · imod tp_or j K ⊤ true e2 e1 $$ Hspec with Hspec
        simp only [↓reduceIte]
        iapply H2 $$ Hspec
    · iintro %v Hv
      iexact Hv
  · apply refines_sound foxtrotSigma
    intro _ Δ
    ihave H1 := refines_typed τ Δ e1 H1
    ihave H2 := refines_typed τ Δ e2 H2
    unfold_rel
    iintro %K %j Hspec
    wp_apply wp_or e2 e1 _ $$ [-]
    · isplit
      · imod tp_or j K ⊤ false e1 e2 $$ Hspec with Hspec
        simp only [Bool.false_eq_true, ↓reduceIte]
        iapply H2 $$ Hspec
      · imod tp_or j K ⊤ true e1 e2 $$ Hspec with Hspec
        simp only [↓reduceIte]
        iapply H1 $$ Hspec
    · iintro %v Hv
      iexact Hv

end eq5

section eq6

/-- Rocq: `eq6`. -/
theorem eq6 (e1 e2 e3 : expr) (τ : type) (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ)
    (H3 : ∅ ⊢ₜ e3 : τ) :
    ∅ ⊨ or e1 (or e2 e3) =ctx= or (or e1 e2) e3 : τ := by
  constructor
  · apply refines_sound foxtrotSigma
    intro _ Δ
    ihave H1 := refines_typed τ Δ e1 H1
    ihave H2 := refines_typed τ Δ e2 H2
    ihave H3 := refines_typed τ Δ e3 H3
    unfold_rel
    iintro %K %j Hspec
    wp_apply wp_or e1 (or e2 e3) _ $$ [-]
    · isplit
      · imod tp_or j K ⊤ true (or e1 e2) e3 $$ Hspec with Hspec
        simp only [↓reduceIte]
        imod tp_or j K ⊤ true e1 e2 $$ Hspec with Hspec
        simp only [↓reduceIte]
        iapply H1 $$ Hspec
      · wp_apply wp_or e2 e3 _ $$ [-]
        · isplit
          · imod tp_or j K ⊤ true (or e1 e2) e3 $$ Hspec with Hspec
            simp only [↓reduceIte]
            imod tp_or j K ⊤ false e1 e2 $$ Hspec with Hspec
            simp only [Bool.false_eq_true, ↓reduceIte]
            iapply H2 $$ Hspec
          · imod tp_or j K ⊤ false (or e1 e2) e3 $$ Hspec with Hspec
            simp only [Bool.false_eq_true, ↓reduceIte]
            iapply H3 $$ Hspec
        · iintro %v Hv
          iexact Hv
    · iintro %v Hv
      iexact Hv
  · apply refines_sound foxtrotSigma
    intro _ Δ
    ihave H1 := refines_typed τ Δ e1 H1
    ihave H2 := refines_typed τ Δ e2 H2
    ihave H3 := refines_typed τ Δ e3 H3
    unfold_rel
    iintro %K %j Hspec
    wp_apply wp_or (or e1 e2) e3 _ $$ [-]
    · isplit
      · wp_apply wp_or e1 e2 _ $$ [-]
        · isplit
          · imod tp_or j K ⊤ true e1 (or e2 e3) $$ Hspec with Hspec
            simp only [↓reduceIte]
            iapply H1 $$ Hspec
          · imod tp_or j K ⊤ false e1 (or e2 e3) $$ Hspec with Hspec
            simp only [Bool.false_eq_true, ↓reduceIte]
            imod tp_or j K ⊤ true e2 e3 $$ Hspec with Hspec
            simp only [↓reduceIte]
            iapply H2 $$ Hspec
        · iintro %v Hv
          iexact Hv
      · imod tp_or j K ⊤ false e1 (or e2 e3) $$ Hspec with Hspec
        simp only [Bool.false_eq_true, ↓reduceIte]
        imod tp_or j K ⊤ false e2 e3 $$ Hspec with Hspec
        simp only [Bool.false_eq_true, ↓reduceIte]
        iapply H3 $$ Hspec
    · iintro %v Hv
      iexact Hv

end eq6

section eq7

/-- Rocq: `eq7`. -/
theorem eq7 (e : expr) (τ : type) (H : ∅ ⊢ₜ e : τ) :
    ∅ ⊨ or e cpl(&diverge #()) =ctx= e : τ := by
  constructor
  · apply refines_sound foxtrotSigma
    intro _ Δ
    ihave H := refines_typed τ Δ e H
    unfold_rel
    iintro %K %j Hspec
    wp_apply wp_or e cpl(&diverge #()) _ $$ [-]
    · isplit
      · iapply H $$ Hspec
      · wp_apply wp_diverge $$ []
        · itrivial
        · iintro %v %Hf
          cases Hf
    · iintro %v Hv
      iexact Hv
  · apply refines_sound foxtrotSigma
    intro _ Δ
    ihave H := refines_typed τ Δ e H
    unfold_rel
    iintro %K %j Hspec
    imod tp_or j K ⊤ true e cpl(&diverge #()) $$ Hspec with Hspec
    simp only [↓reduceIte]
    iapply H $$ Hspec

end eq7

section eq8

/-- Rocq: `eq8`. The other refinement direction is not provable in Foxtrot atm. -/
theorem eq8 (e1 e2 e3 : expr) (p q : ℕ) (τ : type) (H1 : ∅ ⊢ₜ e1 : τ)
    (H2 : ∅ ⊢ₜ e2 : τ)
    (H3 : ∅ ⊢ₜ e3 : τ) :
    ∅ ⊨ or (toss p q e1 e2) (toss p q e1 e3) ≤ctx≤ toss p q e1 (or e2 e3) : τ := by
  apply refines_sound foxtrotSigma
  intro _ Δ
  ihave H1 := refines_typed τ Δ e1 H1
  ihave H2 := refines_typed τ Δ e2 H2
  ihave H3 := refines_typed τ Δ e3 H3
  unfold_rel
  iintro %K %j Hspec
  wp_apply wp_or (toss p q e1 e2) (toss p q e1 e3) _ $$ [-]
  rotate_left
  · iintro %v Hv
    iexact Hv
  · isplit
    · unfold toss
      tp_bind j (Rand _ _)
      wp_apply (wp_couple_rand_rand q (_root_.id) Function.bijective_id j q _
        (Int.toNat_natCast _).symm (fun n hn => hn)) $$ Hspec with %n ⟨%Hn, Hspec⟩
      tp_pures j
      wp_pures
      case_bool_decide <;> tp_pures j <;> wp_pures
      · iapply H1 $$ Hspec
      · imod tp_or j K ⊤ true e2 e3 $$ Hspec with Hspec
        simp only [↓reduceIte]
        iapply H2 $$ Hspec
    · unfold toss
      tp_bind j (Rand _ _)
      wp_apply (wp_couple_rand_rand q (_root_.id) Function.bijective_id j q _
        (Int.toNat_natCast _).symm (fun n hn => hn)) $$ Hspec with %n ⟨%Hn, Hspec⟩
      tp_pures j
      wp_pures
      case_bool_decide <;> tp_pures j <;> wp_pures
      · iapply H1 $$ Hspec
      · imod tp_or j K ⊤ false e2 e3 $$ Hspec with Hspec
        simp only [Bool.false_eq_true, ↓reduceIte]
        iapply H3 $$ Hspec

end eq8

end Foxtrot.Examples.Algebraic
