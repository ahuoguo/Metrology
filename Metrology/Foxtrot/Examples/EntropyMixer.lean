module

public import Metrology.Foxtrot.BinaryRel.BinarySoundness
public import Metrology.Foxtrot.BinaryRel.BinaryRelTactics
public import Metrology.Foxtrot.AdequacyInstance
public import Metrology.Foxtrot.SpecProofMode

/-!
# An entropy mixer

Ported from clutch/theories/foxtrot/examples/entropy_mixer.v

Adding (mod 2) a fair coin to a value read from a location racing with a forked write is
contextually equivalent to a fair coin.

## Rocq → Lean map
* `mixer_prog`, `mixer_refines_rand`, `rand_refines_mixer`, `mixer_eq_rand`: same names
  (namespace `Foxtrot.Examples.EntropyMixer`).
* `` e1 `rem` e2 `` is `e1 % e2`; `rand #1` is `rand(#1)`.
* `foxtrotRΣ` is `foxtrotSigma` (of `Metrology.Foxtrot.AdequacyInstance`), with the local
  instance `foxtrotRGpreS_foxtrotSigma`.

## Deviations
* Rocq's `iIntros (??)` (the `foxtrotRGS` instance and `Δ`) is the binder of `refines_sound`;
  `interp TNat Δ` is unfolded with `dsimp only [interp, lrel_nat]`.
* The coupling bijection of the second case of `mixer_refines_rand` is
  `fun x => if x ≤ 1 then 1 - x else x` (Rocq: `bool_decide (x <= 1)`), and its bijectivity
  (Rocq: the `Unshelve`d goals, including the `le_dec` instance) is the lemma `mixer_f_bij`.
  The other couplings use `id` (Rocq: inferred).
* `Z.rem_small` is `Int.tmod_eq_of_lt`.
* In `rand_refines_mixer`, Rocq's `tp_fork j. iIntros (?) "_"` is `tp_fork j as j' -`.

## Added
* `mixer_f_bij` (see above); `foxtrotRGpreS_foxtrotSigma` (Rocq: `subG_foxtrotRGPreS`).

## Omitted
None.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot Foxtrot.BinaryRel

namespace Foxtrot.Examples.EntropyMixer

/-- Rocq: `subG_foxtrotRGPreS` (at `foxtrotSigma`, Rocq's `foxtrotRΣ`). -/
local instance foxtrotRGpreS_foxtrotSigma : foxtrotRGpreS foxtrotSigma := ⟨inferInstance⟩

/-- Rocq: `mixer_prog`. -/
def mixer_prog : expr := cpl(
  let "y" := ref(#0) in
  fork("y" ← #1);
  let "x1" := !"y" in
  let "x2" := rand(#1) in
  ("x1" + "x2") % #2)

/-- Added (Rocq: the `Unshelve`d goals of `mixer_refines_rand`): the coupling function
`λ x, if bool_decide (x ≤ 1) then 1 - x else x` is a bijection. -/
theorem mixer_f_bij : Function.Bijective (fun x : ℕ => if x ≤ 1 then 1 - x else x) := by
  constructor
  · intro x y h
    simp only at h
    split at h <;> split at h <;> omega
  · intro x
    rcases x with _ | _ | n
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨n + 2, by simp⟩

/-- Rocq: `mixer_refines_rand`. -/
theorem mixer_refines_rand :
    (∅ : varmap type) ⊨ mixer_prog ≤ctx≤ cpl(rand(#1)) : TNat := by
  refine refines_sound foxtrotSigma _ _ _ fun Δ => ?_
  unfold_rel
  iintro %K %j Hspec
  unfold mixer_prog
  wp_alloc l as Hl
  wp_pures
  imod inv_alloc nroot ⊤ iprop(l ↦ LitV (LitInt 0) ∨ l ↦ LitV (LitInt 1)) $$ [Hl] with #Hinv
  · inext
    ileft
    iexact Hl
  wp_apply wp_fork $$ [] [Hspec]
  · iinv Hinv with >H Hclose
    icases H with (H | H)
    · wp_store
      imod Hclose $$ [H]
      · inext
        iright
        iexact H
      imodintro
      itrivial
    · wp_store
      imod Hclose $$ [H]
      · inext
        iright
        iexact H
      imodintro
      itrivial
  wp_pures
  wp_bind (Load _)
  iinv Hinv with >H Hclose
  icases H with (H | H)
  · wp_load
    imod Hclose $$ [H]
    · inext
      ileft
      iexact H
    imodintro
    wp_pures
    wp_apply wp_couple_rand_rand 1 id Function.bijective_id j 1 K (by simp) (fun n hn => hn)
      $$ Hspec with %n ⟨%Hn, Hspec⟩
    wp_pures
    iexists _
    iframe Hspec
    dsimp only [interp, lrel_nat]
    iexists n
    ipureintro
    refine ⟨?_, rfl⟩
    rw [Int.tmod_eq_of_lt (by omega) (by omega)]
  · wp_load
    imod Hclose $$ [H]
    · inext
      iright
      iexact H
    imodintro
    wp_pures
    wp_apply wp_couple_rand_rand 1 (fun x => if x ≤ 1 then 1 - x else x) mixer_f_bij j 1 K
      (by simp) (fun n hn => by split <;> omega) $$ Hspec with %n ⟨%Hn, Hspec⟩
    wp_pures
    iexists _
    iframe Hspec
    dsimp only [interp, lrel_nat]
    iexists 1 - n
    ipureintro
    simp only [Hn, ↓reduceIte, and_true]
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · rfl
    · rfl

/-- Rocq: `rand_refines_mixer`. -/
theorem rand_refines_mixer :
    (∅ : varmap type) ⊨ cpl(rand(#1)) ≤ctx≤ mixer_prog : TNat := by
  refine refines_sound foxtrotSigma _ _ _ fun Δ => ?_
  unfold_rel
  iintro %K %j Hspec
  unfold mixer_prog
  tp_alloc j as l Hl
  tp_pures j
  tp_fork j as j' -
  tp_pures j
  tp_load j
  tp_pures j
  tp_bind j (Rand _ _)
  iapply wp_pupd
  wp_apply wp_couple_rand_rand 1 id Function.bijective_id j 1 _ (by simp) (fun n hn => hn)
    $$ Hspec with %n ⟨%Hn, Hspec⟩
  simp only [id]
  tp_pures j
  imodintro
  iexists _
  iframe Hspec
  dsimp only [interp, lrel_nat]
  iexists n
  ipureintro
  refine ⟨rfl, ?_⟩
  rw [Int.tmod_eq_of_lt (by omega) (by omega)]

/-- Rocq: `mixer_eq_rand`. -/
theorem mixer_eq_rand :
    (∅ : varmap type) ⊨ mixer_prog =ctx= cpl(rand(#1)) : TNat :=
  ⟨mixer_refines_rand, rand_refines_mixer⟩

end Foxtrot.Examples.EntropyMixer
