module

public import Metrology.Foxtrot.BinaryRel.BinaryAdequacyRel
public import Metrology.Foxtrot.BinaryRel.BinaryFundamentalPart5

/-!
# Soundness of Foxtrot's binary logical relation

Ported from clutch/theories/foxtrot/binary_rel/binary_soundness.v

The logical relation is sound with respect to contextual refinement.

## Rocq → Lean map
* `refines_sound_open`, `refines_sound`: same names (namespace `Foxtrot.BinaryRel`).

## Deviations
* The ghost-functor bundle `GF` is explicit (Rocq: `Σ`), and `∀ `{foxtrotRGS Σ} Δ, ..` is
  `∀ [foxtrotRGS GF] (Δ : List (lrel GF)), ..`.
* `lub_termination_prob` is `ℝ≥0∞`-valued, so the Rocq steps `rbar_le_rle`, `Rbar_plus_0_r`
  and `lub_termination_prob_eq` become a single `add_zero` (`foxtrot_rel_adequacy'` is used
  with `ε := 0`).
* The closing step `fmap_empty`/`subst_map_empty` of `refines_sound_open` uses the helper
  `bin_log_related_empty` of `BinaryFundamentalPart4` (which packages `env_ltyped2_empty`,
  `varmap_map_empty` and `subst_map_empty`).

## Omitted
None.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

/-- Rocq: `refines_sound_open`. -/
theorem refines_sound_open (GF : BundledGFunctors) [foxtrotRGpreS GF] (Γ : varmap type)
    (e e' : expr) (τ : type)
    (Hlog : ∀ [foxtrotRGS GF] (Δ : List (lrel GF)), ⊢ 〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ) :
    Γ ⊨ e ≤ctx≤ e' : τ := by
  intro K σ₀ b Htyped
  have h := foxtrot_rel_adequacy' GF (fun [foxtrotRGS GF] => (interp b [] : lrel GF))
    (fun _ _ => True) (fill_ctx K e) (fill_ctx K e') σ₀ σ₀ 0
    (fun _ _ => pure_intro trivial) ?_
  · rwa [add_zero] at h
  · intro _
    have H := bin_log_related_under_typed_ctx (GF := GF) Γ e e' τ ∅ b K Htyped
    have H' : ⊢ 〈([] : List (lrel GF));(∅ : varmap type)〉 ⊨ fill_ctx K e ≤log≤ fill_ctx K e' : b := by
      refine (?_ : ⊢ □ ∀ Δ : List (lrel GF), 〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ).trans
        (H.trans (forall_elim []))
      imodintro
      iintro %Δ
      iapply Hlog Δ
    exact true_intro.trans (bin_log_related_empty [] _ _ b H')

/-- Rocq: `refines_sound`. -/
theorem refines_sound (GF : BundledGFunctors) [foxtrotRGpreS GF] (e e' : expr) (τ : type)
    (Hlog : ∀ [foxtrotRGS GF] (Δ : List (lrel GF)), ⊢ REL e << e' : interp τ Δ) :
    (∅ : varmap type) ⊨ e ≤ctx≤ e' : τ := by
  refine refines_sound_open GF ∅ e e' τ fun Δ => ?_
  unfold bin_log_related
  simp only [varmap_map_empty]
  iintro %vs Hvs
  ihave %Hvs := env_ltyped2_empty_inv vs $$ Hvs
  subst Hvs
  simp only [varmap_map_empty, subst_map_empty]
  iapply Hlog Δ

end Foxtrot.BinaryRel
