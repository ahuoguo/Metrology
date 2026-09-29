module

public import Metrology.Coneris.Examples.ParallelAdd

/-!
# Parallel additions of coin flips (part 4)

Ported from clutch/theories/coneris/examples/parallel_add.v (the namespaces `loc_nroot`,
`both_nroot`, the programs `half_FAA'`, `parallel_add'`, and section `attempt3`: a hocap style
spec for `half_FAA'` and `parallel_add_spec'''`)

See `ParallelAdd` for the Rocq → Lean map. `α ↪B bs` is `Coneris.Lib.Flip.bool_tape`;
`frac_authF` is the functor of `inG Σ (frac_authR ZR)`.

## Proofs that differ from Rocq
* `iMod (own_alloc (●F 0 ⋅ ◯F 0))` is `ghost_var_alloc_frac 0`; splitting `◯F 0` into two
  `◯F{1/2} 0` and combining two `◯F{1/2} 1` into `◯F 2` (Rocq: implicit, by `frac_auth_frag_op`)
  are the helpers `own_fragF_op`, `own_fragF_halves`.
* Rocq's folding `rewrite` of `half_FAA' l α` is a `rw` with an `rfl` equation; the closed
  `allocB` is kept through the substitutions with the helper `subst_allocB`.
* The error side conditions of `wp_presample_bool_adv_comp` are proved by `simp`/`toReal`.

## Added
`subst_allocB`, `own_fragF_op`, `own_fragF_halves`.

## Omitted
Nothing (from any of the four parts). `both_nroot` is unused, as in Rocq.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par Coneris.Lib.Flip

namespace Coneris.Examples.ParallelAdd

/-- Rocq: `loc_nroot`. -/
def loc_nroot : Namespace := ndot nroot "loc"

/-- Rocq: `both_nroot`. -/
def both_nroot : Namespace := ndot nroot "both"

/-- Rocq: `half_FAA'`. -/
def half_FAA' (l α : Loc) : expr := cpl(if &flipL #lbl(α) then faa(#l, #1) else #())

/-- Rocq: `parallel_add'`. -/
def parallel_add' : expr := cpl(
  let r := ref(#0) in
  let α := &allocB in
  let α' := &allocB in
  ((if &flipL α then faa(r, #1) else #())
   ‖
   (if &flipL α' then faa(r, #1) else #()));
  !r)

/-- Helper: `allocB` is closed. -/
theorem subst_allocB (x : String) (v : val) : subst x v allocB = allocB := rfl

section attempt3

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [ElemG GF frac_authF]

/-- Helper: `own γ (◯F{q1 + q2} (a1 + a2)) ⊣⊢ own γ (◯F{q1} a1) ∗ own γ (◯F{q2} a2)` (Rocq:
`frac_auth_frag_op`, used implicitly by `iDestruct`/`iCombine`). -/
theorem own_fragF_op (γ : GName) (q1 q2 : Qp) (a1 a2 : ZR) :
    own_fragF (GF := GF) γ (q1 + q2) (a1 + a2) ⊣⊢ own_fragF γ q1 a1 ∗ own_fragF γ q2 a2 := by
  rw [← iOwn_op.to_eq]
  exact (congrArg (iOwn (F := frac_authF) γ) FracAuth.frag_op).to_bi

/-- Helper: `own γ (◯F z) ⊣⊢ own γ (◯F{1/2} z1) ∗ own γ (◯F{1/2} z2)` for `z = z1 + z2`. -/
theorem own_fragF_halves (γ : GName) (z z1 z2 : ZR) (hz : z = z1 + z2) :
    own_fragF (GF := GF) γ 1 z ⊣⊢
      own_fragF γ (1 : Qp).half z1 ∗ own_fragF γ (1 : Qp).half z2 := by
  have h := own_fragF_op (GF := GF) γ (1 : Qp).half (1 : Qp).half z1 z2
  rw [Qp.half_add_half, ← hz] at h
  exact h

/-- Rocq: `wp_half_FAA'`. A hocap style spec for `half_FAA'`. -/
theorem wp_half_FAA' (E : CoPset) (P Q : IProp GF) (γ : GName) (l α : Loc) (bs : List Bool)
    (Hsubset : ↑loc_nroot ⊆ E) :
    {{ inv loc_nroot iprop(∃ z : ℤ, l ↦ LitV (LitInt z) ∗ own_authF γ z) ∗
        □ (∀ z : ℤ, P ∗ own_authF γ z ={E \ ↑loc_nroot}=∗ own_authF γ (z + 1) ∗ Q) ∗
        P ∗ α ↪B (true :: bs) }} (half_FAA' l α) @ E
    {{ v, RET v; α ↪B bs ∗ Q }} := by
  iintro %Φ ⟨#Hinv, #Hchange, HP, Hα⟩ HΦ
  unfold half_FAA'
  wp_apply wp_flipL E α true bs $$ [Hα] with Hα
  · iexact Hα
  wp_pures
  iinv Hinv with ⟨%z, >Hl, >Hauth⟩ Hclose
  wp_faa
  imod Hchange $$ [HP Hauth] with ⟨Hauth, HQ⟩
  · iframe
  imod Hclose $$ [Hl Hauth]
  · inext
    iexists z + 1
    iframe
  imodintro
  iapply HΦ
  iframe

/-- Rocq: `parallel_add_spec'''`. -/
theorem parallel_add_spec''' :
    {{ ↯ (3 / 4) }} parallel_add'
    {{ (z : ℤ), RET LitV (LitInt z); (⌜z = 2⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold parallel_add'
  wp_alloc l as Hl
  wp_pures
  simp only [subst_allocB]
  wp_apply wp_allocB_tape ⊤ $$ [] with %α Hα
  · itrivial
  wp_pures
  simp only [subst_allocB]
  wp_apply wp_allocB_tape ⊤ $$ [] with %α' Hα'
  · itrivial
  wp_pures
  -- Create location RA
  imod ghost_var_alloc_frac 0 with ⟨%γ, Hauth_loc, Hfrag_loc⟩
  -- Allocate location inv
  imod inv_alloc loc_nroot ⊤ iprop(∃ z : ℤ, l ↦ LitV (LitInt z) ∗ own_authF γ z)
    $$ [Hl Hauth_loc] with #Hlocinv
  · inext
    iexists 0
    iframe
  ihave ⟨Hfrac_a, Hfrac_b⟩ := (own_fragF_halves γ 0 0 0 rfl).mp $$ Hfrag_loc
  -- presample
  iapply wp_presample_bool_adv_comp ⊤ _ α _ [] (3 / 4) (fun b => if b then 1 / 2 else 1)
    (by
      simp only [↓reduceIte, Bool.false_eq_true]
      rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness), ENNReal.toReal_div,
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
      norm_num)
  isplitl [Hα]
  · inext
    iexact Hα
  isplitl [Herr]
  · iexact Herr
  iintro %b ⟨Herr, Hα⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Herr
  simp only [↓reduceIte, List.nil_append]
  iapply wp_presample_bool_adv_comp ⊤ _ α' _ [] (1 / 2) (fun b => if b then 0 else 1)
    (by simp)
  isplitl [Hα']
  · inext
    iexact Hα'
  isplitl [Herr]
  · iexact Herr
  iintro %b ⟨Herr, Hα'⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Herr
  simp only [List.nil_append]
  wp_apply wp_par' (fun _ => own_fragF γ (1 : Qp).half 1) (fun _ => own_fragF γ (1 : Qp).half 1)
    $$ [Hfrac_a Hα] [Hfrac_b Hα']
  · rw [show cpl(if v(&flipL) #lbl(α) then faa(#l, #1) else #()) = half_FAA' l α from rfl]
    wp_apply wp_half_FAA' ⊤ (own_fragF γ (1 : Qp).half 0) (own_fragF γ (1 : Qp).half 1) γ l α []
      CoPset.subseteq_top $$ [Hfrac_a Hα] with %v ⟨-, HQ⟩
    · iframe Hfrac_a Hα
      isplit
      · iexact Hlocinv
      imodintro
      iintro %z ⟨Hfrac, Hauth⟩
      imod ghost_var_update_frac γ 1 z 0 _ $$ Hauth Hfrac with ⟨Hauth, Hfrac⟩
      imodintro
      rw [zero_add]
      iframe
    iexact HQ
  · rw [show cpl(if v(&flipL) #lbl(α') then faa(#l, #1) else #()) = half_FAA' l α' from rfl]
    wp_apply wp_half_FAA' ⊤ (own_fragF γ (1 : Qp).half 0) (own_fragF γ (1 : Qp).half 1) γ l α' []
      CoPset.subseteq_top $$ [Hfrac_b Hα'] with %v ⟨-, HQ⟩
    · iframe Hfrac_b Hα'
      isplit
      · iexact Hlocinv
      imodintro
      iintro %z ⟨Hfrac, Hauth⟩
      imod ghost_var_update_frac γ 1 z 0 _ $$ Hauth Hfrac with ⟨Hauth, Hfrac⟩
      imodintro
      rw [zero_add]
      iframe
    iexact HQ
  · iintro %v1 %v2 ⟨Hfrac_a, Hfrac_b⟩
    ihave Hfrac := (own_fragF_halves γ 2 1 1 rfl).mpr $$ [Hfrac_a Hfrac_b]
    · iframe
    inext
    wp_pures
    iinv Hlocinv with ⟨%z, >Hl, >Hauth⟩ Hclose
    ihave %Heq := ghost_var_agree_frac $$ Hauth Hfrac
    subst Heq
    wp_load
    imod Hclose $$ [Hl Hauth]
    · inext
      iexists 2
      iframe
    iapply HΦ
    ipureintro
    rfl

end attempt3

end Coneris.Examples.ParallelAdd
