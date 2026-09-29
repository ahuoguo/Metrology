module

public import Metrology.Foxtrot.Examples.VonNeumannPart2
public import Metrology.Foxtrot.Examples.VonNeumannPart3

/-!
# The von Neumann trick: from the concurrent program to the concurrent tape program

Ported from clutch/theories/foxtrot/examples/von_neumann.v (part 4:
`wp_von_neumann_con_prog_von_neumann_con_prog'`). The deviations listed here also apply to
`VonNeumannPart5`.

## Rocq → Lean map
* All lemmas: same names.
* `binary_fundamental.refines_typed` is used through the helper `wp_ad_fork` (of
  `VonNeumann`), which packages the forked-adversary part of both proofs.
* Rocq's `apply (refines_sound (#[foxtrotRΣ]))` / `(#[spawnΣ; foxtrotRΣ])` (in
  `VonNeumannPart5`) are `refines_sound foxtrotSigma` / `refines_sound vonNeumannSigma`.
* The final comparison `#b1 = #b2` of the spec (resp. LHS) is stepped with a single
  `tp_pure` / `wp_pure` in the looping case, so that the Löb hypothesis applies to the
  unrolled call (Rocq: `tp_pure j. wp_pure.`).

## Deviations
* In `wp_von_neumann_con_prog_von_neumann_con_prog'`, the postconditions of `wp_par` are as in
  Rocq (`∃ b : bool, ⌜v = #b⌝ ∗ j1 ⤇ fill K1 v`); in
  `wp_von_neumann_con_prog'_von_neumann_prog` Rocq's `⌜v = #(bool_decide (x ≤ n `min` N))⌝` is
  `⌜v = #(decide (x ≤ m))⌝` with `m = min n N` (the `ℤ` minimum is rewritten into the
  natural-number one, `Nat.cast_min`).
* `case_bool_decide` on the final comparison is `by_cases` on the equality of the two booleans
  (then `decide_eq_true` / `decide_eq_false`).
* `(TUnit → TBool)` is `TArrow TUnit TBool`; the refinements are stated for the applications
  `von_neumann_prog N ad` etc. (Rocq: `von_neumann_prog ad`, `N` being a section variable).

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

/-- Rocq: `wp_von_neumann_con_prog_von_neumann_con_prog'`. -/
theorem wp_von_neumann_con_prog_von_neumann_con_prog' (Ht : Htyped ad) (K : List ectx_item)
    (j : ℕ) :
    ⊢ j ⤇ fill K cpl(&(von_neumann_con_prog' N) &ad) -∗
      WP cpl(&(von_neumann_con_prog N) &ad)
        {{ v, ∃ v' : val, j ⤇ fill K (Val v') ∗
          (lrel_arr lrel_unit lrel_bool : lrel GF) v v' }} := by
  iintro Hspec
  unfold von_neumann_con_prog' von_neumann_con_prog
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
  tp_allocnattape j'' α as Hα
  tp_pures j''
  tp_allocnattape j'' β as Hβ
  tp_pure j''
  tp_pure j''
  tp_bind j'' (App (App (Val par) _) _)
  imod tp_par $$ Hspec with ⟨%j1, %j2, %K1, %K2, Hspec1, Hspec2, Hcont⟩
  wp_bind (App (App (Val par) _) _)
  wp_apply wp_par
      (fun v => iprop(∃ b : Bool, ⌜v = LitV (LitBool b)⌝ ∗ j1 ⤇ fill K1 (Val v)))
      (fun v => iprop(∃ b : Bool, ⌜v = LitV (LitBool b)⌝ ∗ j2 ⤇ fill K2 (Val v)))
      $$ [Hα Hspec1] [Hβ Hspec2]
  · tp_bind j1 (Rand _ _)
    wp_bind (Rand _ _)
    wp_apply wp_couple_rand_rand_lbl (N + 1) id Function.bijective_id ((N + 1 : ℕ) : ℤ) _ α
      j1 (by simp) (fun n hn => hn) $$ [Hα Hspec1] with %x ⟨-, Hspec1, %Hx⟩
    · iframe Hα Hspec1
    simp only [id]
    tp_pures j1
    wp_pures
    iexists _
    iframe Hspec1
    ipureintro
    rfl
  · tp_bind j2 (Rand _ _)
    wp_bind (Rand _ _)
    wp_apply wp_couple_rand_rand_lbl (N + 1) id Function.bijective_id ((N + 1 : ℕ) : ℤ) _ β
      j2 (by simp) (fun n hn => hn) $$ [Hβ Hspec2] with %x ⟨-, Hspec2, %Hx⟩
    · iframe Hβ Hspec2
    simp only [id]
    tp_pures j2
    wp_pures
    iexists _
    iframe Hspec2
    ipureintro
    rfl
  iintro %w1 %w2 ⟨⟨%b1, %h1, Hspec1⟩, ⟨%b2, %h2, Hspec2⟩⟩
  subst h1 h2
  inext
  imod Hcont $$ %_ %_ %⊤ [Hspec1 Hspec2] with Hspec
  · iframe Hspec1 Hspec2
  tp_pures j''
  wp_pures
  by_cases h : b1 = b2
  · rw [decide_eq_true h]
    tp_pure j''
    wp_pure
    iapply IH $$ Hspec
  · rw [decide_eq_false h]
    tp_pures j''
    wp_pure
    iexists _
    iframe Hspec
    dsimp only [lrel_bool]
    iexists b1
    ipureintro
    exact ⟨rfl, rfl⟩

end proof'

end Foxtrot.Examples.VonNeumann
