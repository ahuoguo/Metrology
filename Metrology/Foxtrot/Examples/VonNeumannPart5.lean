module

public import Metrology.Foxtrot.Examples.VonNeumannPart4

/-!
# The von Neumann trick: the last concurrent step and the contextual equivalence

Ported from clutch/theories/foxtrot/examples/von_neumann.v (part 5:
`wp_von_neumann_con_prog'_von_neumann_prog`, `von_neumann_prog_refines_rand_prog`,
`rand_prog_refines_von_neumann_prog`, `von_neumann_prog_eq_rand_prog`).

See `VonNeumannPart4` for the deviations; additionally:
* `pupd_couple_tape_rand` takes the bijection `id` explicitly (Rocq: inferred).

## Omitted
None.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot Foxtrot.BinaryRel Foxtrot.Lib.Spawn Foxtrot.Lib.Par Foxtrot.Lib.Min
open Foxtrot.Lib.Conversion

namespace Foxtrot.Examples.VonNeumann

section proof'

variable (N : ℕ) (ad : val)
variable {GF : BundledGFunctors} [foxtrotRGS GF] [spawnG GF]

/-- Rocq: `wp_von_neumann_con_prog'_von_neumann_prog`. -/
theorem wp_von_neumann_con_prog'_von_neumann_prog (Ht : Htyped ad) (K : List ectx_item)
    (j : ℕ) :
    ⊢ j ⤇ fill K cpl(&(von_neumann_prog N) &ad) -∗
      WP cpl(&(von_neumann_con_prog' N) &ad)
        {{ v, ∃ v' : val, j ⤇ fill K (Val v') ∗
          (lrel_arr lrel_unit lrel_bool : lrel GF) v v' }} := by
  iintro Hspec
  unfold von_neumann_con_prog' von_neumann_prog
  wp_pures
  tp_pures j
  wp_alloc l as Hl
  tp_alloc j as l' Hl'
  wp_pures
  tp_pures j
  imod inv_alloc (logN.@ (l, l')) ⊤
      iprop(∃ v0 v3 : val, l ↦ v0 ∗ l' ↦ₛ v3 ∗ (lrel_nat : lrel GF) v0 v3) $$ [Hl Hl']
    with #Hinv
  · inext
    iexists _, _
    iframe Hl Hl'
    dsimp only [lrel_nat]
    iexists 0
    ipureintro
    exact ⟨rfl, rfl⟩
  tp_fork j as j' Hspec'
  wp_apply wp_fork $$ [Hspec']
  · iapply wp_ad_fork ad Ht $$ Hinv Hspec'
  tp_pures j
  wp_pures
  iexists _
  iframe Hspec
  imodintro
  dsimp only [lrel_arr, lrel_unit]
  imodintro
  iintro %v1 %v2 %⟨h1, h2⟩
  subst h1 h2
  unfold BinaryRel.refines BinaryRel.refines_def
  iintro %K' %j'' Hspec
  iloeb as IH generalizing Hspec
  wp_pures
  tp_pures j''
  wp_bind (Load _)
  dsimp only [lrel_nat]
  iinv Hinv with ⟨%v0, %v3, >Hl, >Hl', >⟨%n, %h1, %h2⟩⟩ Hclose
  subst h1 h2
  tp_load j''
  wp_load
  imod Hclose $$ [Hl Hl']
  · inext
    iexists _, _
    iframe Hl Hl'
    iexists n
    ipureintro
    exact ⟨rfl, rfl⟩
  imodintro
  tp_bind j'' (App (App (Val min_prog) _) _)
  imod spec_min_prog ⊤ j'' _ (n : ℤ) (N : ℤ) $$ Hspec with Hspec
  wp_apply wp_min_prog (n : ℤ) (N : ℤ) ⊤ $$ [] with %z %Hz
  · itrivial
  subst Hz
  rw [← Nat.cast_min]
  obtain ⟨m, hmeq⟩ : ∃ m, min n N = m := ⟨_, rfl⟩
  rw [hmeq]
  wp_pures
  tp_pures j''
  wp_alloctape α as Hα
  wp_pures
  wp_alloctape β as Hβ
  wp_pures
  tp_bind j'' (Rand _ _)
  imod pupd_couple_tape_rand (N + 1) id Function.bijective_id _ ⊤ α ((N + 1 : ℕ) : ℤ) [] j''
      (by simp) (fun n hn => hn) $$ [Hα] Hspec with ⟨%x, Hα, Hspec, %Hx⟩
  · inext
    iexact Hα
  simp only [id, List.nil_append]
  tp_pures j''
  tp_bind j'' (Rand _ _)
  imod pupd_couple_tape_rand (N + 1) id Function.bijective_id _ ⊤ β ((N + 1 : ℕ) : ℤ) [] j''
      (by simp) (fun n hn => hn) $$ [Hβ] Hspec with ⟨%y, Hβ, Hspec, %Hy⟩
  · inext
    iexact Hβ
  simp only [id, List.nil_append]
  tp_pures j''
  wp_bind (App (App (Val par) _) _)
  wp_apply wp_par (fun v => iprop(⌜v = LitV (LitBool (decide (x ≤ m)))⌝))
      (fun v => iprop(⌜v = LitV (LitBool (decide (y ≤ m)))⌝)) $$ [Hα] [Hβ]
  · wp_randtape
    wp_pures
    ipureintro
    rfl
  · wp_randtape
    wp_pures
    ipureintro
    rfl
  iintro %w1 %w2 ⟨%h1, %h2⟩
  subst h1 h2
  inext
  wp_pures
  by_cases h : (x ≤ m ↔ y ≤ m)
  · simp only [decide_eq_decide.mpr h, beq_self_eq_true]
    tp_pure j''
    wp_pure
    iapply IH $$ Hspec
  · simp only [beq_eq_false_iff_ne.mpr (fun e => h (decide_eq_decide.mp e))]
    tp_pures j''
    wp_pure
    iexists _
    iframe Hspec
    dsimp only [lrel_bool]
    iexists _
    ipureintro
    exact ⟨rfl, rfl⟩

end proof'

section refinements

variable (N : ℕ) (ad : val)

/-- Rocq: `von_neumann_prog_refines_rand_prog`. -/
theorem von_neumann_prog_refines_rand_prog (Ht : Htyped ad) :
    (∅ : varmap type) ⊨ cpl(&(von_neumann_prog N) &ad) ≤ctx≤ cpl(&rand_prog &ad) :
      TArrow TUnit TBool := by
  refine ctx_refines_transitive _ _ _ cpl(&(von_neumann_prog' N) &ad) _ ?_ ?_ <;>
    refine refines_sound foxtrotSigma _ _ _ fun Δ => ?_
  · unfold BinaryRel.refines BinaryRel.refines_def
    simp only [interp_TArrow, interp_TUnit, interp_TBool]
    iintro %K %j Hspec
    iapply wp_von_neumann_prog_von_neumann_prog' N ad Ht K j $$ Hspec
  -- Rocq: "this one needs stronger logical relations!"
  · unfold BinaryRel.refines BinaryRel.refines_def
    simp only [interp_TArrow, interp_TUnit, interp_TBool]
    iintro %K %j Hspec
    iapply wp_von_neumann_prog'_rand_prog N ad Ht K j $$ Hspec

/-- Rocq: `rand_prog_refines_von_neumann_prog`. -/
theorem rand_prog_refines_von_neumann_prog (Ht : Htyped ad) :
    (∅ : varmap type) ⊨ cpl(&rand_prog &ad) ≤ctx≤ cpl(&(von_neumann_prog N) &ad) :
      TArrow TUnit TBool := by
  refine ctx_refines_transitive _ _ _ cpl(&rand_prog' &ad) _ ?_
    (ctx_refines_transitive _ _ _ cpl(&(von_neumann_con_prog N) &ad) _ ?_
      (ctx_refines_transitive _ _ _ cpl(&(von_neumann_con_prog' N) &ad) _ ?_ ?_)) <;>
    refine refines_sound vonNeumannSigma _ _ _ fun Δ => ?_
  · unfold BinaryRel.refines BinaryRel.refines_def
    simp only [interp_TArrow, interp_TUnit, interp_TBool]
    iintro %K %j Hspec
    iapply wp_rand_prog_rand_prog' ad Ht K j $$ Hspec
  · unfold BinaryRel.refines BinaryRel.refines_def
    simp only [interp_TArrow, interp_TUnit, interp_TBool]
    iintro %K %j Hspec
    iapply wp_rand_prog'_von_neumann_con_prog N ad Ht K j $$ Hspec
  · unfold BinaryRel.refines BinaryRel.refines_def
    simp only [interp_TArrow, interp_TUnit, interp_TBool]
    iintro %K %j Hspec
    iapply wp_von_neumann_con_prog_von_neumann_con_prog' N ad Ht K j $$ Hspec
  · unfold BinaryRel.refines BinaryRel.refines_def
    simp only [interp_TArrow, interp_TUnit, interp_TBool]
    iintro %K %j Hspec
    iapply wp_von_neumann_con_prog'_von_neumann_prog N ad Ht K j $$ Hspec

/-- Rocq: `von_neumann_prog_eq_rand_prog`. -/
theorem von_neumann_prog_eq_rand_prog (Ht : Htyped ad) :
    (∅ : varmap type) ⊨ cpl(&(von_neumann_prog N) &ad) =ctx= cpl(&rand_prog &ad) :
      TArrow TUnit TBool :=
  ⟨von_neumann_prog_refines_rand_prog N ad Ht, rand_prog_refines_von_neumann_prog N ad Ht⟩

end refinements

end Foxtrot.Examples.VonNeumann
