module

public import Metrology.Foxtrot.Examples.Algebraic

/-!
# Algebraic theory (part 2: steps of `eq3` without concurrency)

Ported from clutch/theories/foxtrot/examples/algebraic.v (section `eq3`).

## Rocq → Lean map
* `eq3_step_tapes`: the first `ctx_refines_transitive` step of `eq3_1` ("no tape to tapes",
  `toss r s (toss p q e1 e2) e3` to the program with two tapes); also the second step of
  `eq3_2` (instantiated at renamed parameters).
* `eq3_step_flip`: the first step of `eq3_2` (and its fifth step, instantiated), coupling both
  `rand`s along `flip_bij`.
See `Metrology.Foxtrot.Examples.Algebraic` for the general deviations.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel Foxtrot.Lib.Toss

namespace Foxtrot.Examples.Algebraic

section eq3

/-- The first step of the Rocq proofs of `eq3_1` (and second of `eq3_2`). -/
theorem eq3_step_tapes (e1 e2 e3 : expr) (τ : type) (p q r s : ℕ)
    (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) (H3 : ∅ ⊢ₜ e3 : τ) :
    ∅ ⊨ toss r s (toss p q e1 e2) e3 ≤ctx≤
      cpl(let α := alloc(#s);
          let β := alloc(#q);
          if rand(α) #s < #r
          then if rand(β) #q < #p then &e1 else &e2
          else &e3) : τ := by
  apply refines_sound foxtrotSigma
  intro _ Δ
  ihave H1 := refines_typed τ Δ e1 H1
  ihave H2 := refines_typed τ Δ e2 H2
  ihave H3 := refines_typed τ Δ e3 H3
  unfold_rel
  iintro %K %j Hspec
  tp_allocnattape j α as Hα
  tp_pures j
  tp_allocnattape j β as Hβ
  tp_pures j
  unfold toss
  solve_subst
  tp_bind j (Rand _ _)
  wp_apply (wp_couple_rand_rand_lbl s _root_.id Function.bijective_id s _ α j
    (Int.toNat_natCast _).symm (fun n hn => hn)) $$ [Hα Hspec] with %n ⟨-, Hspec, %Hn⟩
  · iframe Hα Hspec
  tp_pures j
  wp_pures
  case_bool_decide <;> wp_pures <;> tp_pures j
  · tp_bind j (Rand _ _)
    wp_apply (wp_couple_rand_rand_lbl q _root_.id Function.bijective_id q _ β j
      (Int.toNat_natCast _).symm (fun n hn => hn)) $$ [Hβ Hspec] with %m ⟨-, Hspec, %Hm⟩
    · iframe Hβ Hspec
    tp_pures j
    wp_pures
    case_bool_decide <;> wp_pures <;> tp_pures j
    · iapply H1 $$ Hspec
    · iapply H2 $$ Hspec
  · iapply H3 $$ Hspec

/-- The first (and fifth) step of the Rocq proof of `eq3_2`. -/
theorem eq3_step_flip (e1 e2 e3 : expr) (τ : type) (p q r s : ℕ)
    (H1 : ∅ ⊢ₜ e1 : τ) (H2 : ∅ ⊢ₜ e2 : τ) (H3 : ∅ ⊢ₜ e3 : τ) :
    ∅ ⊨ toss p q e1 (toss r s e2 e3) ≤ctx≤
      toss (q + 1 - p) q (toss (s + 1 - r) s e3 e2) e1 : τ := by
  apply refines_sound foxtrotSigma
  intro _ Δ
  ihave H1 := refines_typed τ Δ e1 H1
  ihave H2 := refines_typed τ Δ e2 H2
  ihave H3 := refines_typed τ Δ e3 H3
  unfold_rel
  iintro %K %j Hspec
  unfold toss
  tp_bind j (Rand _ _)
  wp_apply (wp_couple_rand_rand q (flip_bij q) (flip_bij_bij q) j q _
    (Int.toNat_natCast _).symm (flip_bij_dom q)) $$ Hspec with %n ⟨%Hn, Hspec⟩
  rw [flip_bij_le q n Hn]
  wp_pures
  tp_pures j
  case_bool_decide <;> case_bool_decide <;> try omega
  all_goals wp_pures; tp_pures j
  all_goals first
    | iapply H1 $$ Hspec
    | tp_bind j (Rand _ _)
      wp_apply (wp_couple_rand_rand s (flip_bij s) (flip_bij_bij s) j s _
        (Int.toNat_natCast _).symm (flip_bij_dom s)) $$ Hspec with %m ⟨%Hm, Hspec⟩
      rw [flip_bij_le s m Hm]
      wp_pures
      tp_pures j
      case_bool_decide <;> case_bool_decide <;> try omega
      all_goals wp_pures; tp_pures j
      all_goals first
        | iapply H2 $$ Hspec
        | iapply H3 $$ Hspec

end eq3

end Foxtrot.Examples.Algebraic
