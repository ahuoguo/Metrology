module

public import Metrology.Coneris.Lib.Par
public import Metrology.Coneris.Lib.Flip
public import Iris.Algebra.Lib.ExclAuth
public import Iris.Instances.Lib.CInvariants

/-!
# Message passing through a racy location

Ported from clutch/theories/coneris/examples/message_pass.v

One thread flips a coin and writes `0`/`1` to `l`; the other spins until `l ≠ -1` and returns
it. Spending `↯ (1/2)` on the flip, the final content of `l` is `0`.

## Rocq → Lean map
* Namespace `Coneris.Examples.MessagePass`; `prog`, `prog_spec` keep their names.
* `conerisGS Σ, spawnG Σ, inG Σ (excl_authR boolO), cinvG Σ` are `[conerisGS GF] [spawnG GF]
  [ElemG GF excl_authTF] [CInvG GF]` with `excl_authTF := constOF (ExclAuthR (A := DiscreteO
  Bool))`; `own γ (●E b)`/`own γ (◯E b)` are the abbreviations `own_auth γ b`/`own_frag γ b`.
* `cinv_alloc`, `cinv_acc_strong`, `cinv_cancel`, `cinv_own` are iris-lean's
  `CancelableInvariant.alloc`, `.acc_strong`, `.cancel`, `.own`; `1/2 : Qp` is
  `(1 : Qp).half`. `rewrite -union_difference_L` is `rw [LawfulSet.subset_union_diff ..]`.
* `e1 ||| e2` is the local program notation `e1 ‖ e2` (as in `Coneris.Examples.TwoDie`), and
  `wp_par` is applied through the helper `wp_par'` (`par_V` unfolded).
* `↯ (/2)` is `↯ 2⁻¹` in `ℝ≥0∞`; the error function of `wp_flip_adv` is `ℝ≥0∞`-valued (its
  nonnegativity side goal vanishes); `(1/2) * (0 + 1) = 1/2` is `norm_num`.
* `!(#l)` is written `(!#l)` (a prefix `!` cannot start an application argument in `cpl`).

## Proofs that differ from Rocq
* The inline ghost-state reasoning (`own_alloc`/`excl_auth_valid`, `iCombine .. gives` +
  `excl_auth_agree_L`, `own_update_2`/`excl_auth_update`) is factored into the helpers
  `ghost_var_alloc`, `ghost_var_agree`, `ghost_var_update`; the splitting/combining of
  `cinv_own γ 1` into halves (Rocq: `Fractional`, `iDestruct "Hc" as "[Hc Hc']"`/`iCombine`) is
  the helper `cinv_own_halves`.
* The Löb induction generalizes the fraction `Hc'` (`iloeb as IH generalizing Hc'`), as Rocq's
  `iLöb` does for the spatial context.

## Added
`‖` notation, `wp_par'`, `excl_authTF`, `own_auth`, `own_frag`, `ghost_var_alloc`,
`ghost_var_agree`, `ghost_var_update`, `cinv_own_halves` (helpers).

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par Coneris.Lib.Flip
open Iris.ExclAuth Iris.CancelableInvariant

namespace Coneris.Examples.MessagePass

/-- `e1 ||| e2` (Rocq: `par (λ: <>, e1)%E (λ: <>, e2)%E` in `expr_scope`) as a program
notation. -/
scoped syntax:55 cpl_exp:56 " ‖ " cpl_exp:55 : cpl_exp

macro_rules
  | `(cpl($e1 ‖ $e2)) => `(cpl(&par (λ <>, $e1) (λ <>, $e2)))

/-- Helper (not in Rocq): `wp_par` with `par_V` unfolded, so that `wp_apply` finds it. -/
theorem wp_par' {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]
    (Ψ1 Ψ2 : val → IProp GF) (e1 e2 : expr) (Φ : val → IProp GF) :
    ⊢ WP e1 {{ Ψ1 }} -∗ WP e2 {{ Ψ2 }} -∗
      (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (PairV v1 v2)) -∗
      WP cpl(&par v(λ <>, &e1) v(λ <>, &e2)) {{ Φ }} :=
  wp_par Ψ1 Ψ2 e1 e2 Φ

/-- Rocq: `prog`. -/
def prog (l : Loc) : expr := cpl(
  #l ← #(-1);
  ((if &flip then #l ← #0 else #l ← #1) ‖
   (v(rec f y :=
        if y = #(-1)
        then f (!#l)
        else y) (!#l))))

/-- Rocq: the functor of `inG Σ (excl_authR boolO)`. -/
abbrev excl_authTF : COFE.OFunctorPre := constOF (ExclAuthR (A := DiscreteO Bool))

section proof

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [ElemG GF excl_authTF] [CInvG GF]

/-- `own γ (●E b)`. -/
abbrev own_auth (γ : GName) (b : Bool) : IProp GF :=
  iOwn (F := excl_authTF) γ (●E (⟨b⟩ : DiscreteO Bool))

/-- `own γ (◯E b)`. -/
abbrev own_frag (γ : GName) (b : Bool) : IProp GF :=
  iOwn (F := excl_authTF) γ (◯E (⟨b⟩ : DiscreteO Bool))

/-- Helper: `own_alloc (●E b ⋅ ◯E b)` (Rocq: inline, with `excl_auth_valid`). -/
theorem ghost_var_alloc (b : Bool) : ⊢@{IProp GF} |==> ∃ γ, own_auth γ b ∗ own_frag γ b := by
  imod iOwn_alloc (F := excl_authTF) ((●E (⟨b⟩ : DiscreteO Bool)) • (◯E (⟨b⟩ : DiscreteO Bool)))
    ExclAuth.valid with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe

/-- Helper: `iCombine .. gives %K; excl_auth_agree_L` (Rocq: inline). -/
theorem ghost_var_agree (γ : GName) (b c : Bool) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c -∗ ⌜b = c⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree H)

/-- Helper: `own_update_2 .. excl_auth_update` (Rocq: inline). -/
theorem ghost_var_update (γ : GName) (b' b c : Bool) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c ==∗ own_auth γ b' ∗ own_frag γ b' := by
  iintro H1 H2
  ihave H := (iOwn_op (F := excl_authTF)).2 $$ [H1 H2]
  · iframe
  imod iOwn_update ExclAuth.update $$ H with ⟨H1, H2⟩
  imodintro
  iframe

/-- Helper: `cinv_own γ 1 ⊣⊢ cinv_own γ (1/2) ∗ cinv_own γ (1/2)` (Rocq: by `Fractional`). -/
theorem cinv_own_halves (γ : GName) :
    CancelableInvariant.own (GF := GF) γ 1 ⊣⊢
      CancelableInvariant.own γ (1 : Qp).half ∗ CancelableInvariant.own γ (1 : Qp).half := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (instFractionalOwn γ).fractional _ _

/-- Rocq: `prog_spec`. -/
theorem prog_spec (l : Loc) :
    {{ ↯ (2⁻¹ : ℝ≥0∞) ∗ ∃ v, l ↦ v }} (prog l)
    {{ v, RET v; (l ↦ LitV (LitInt 0) : IProp GF) }} := by
  iintro %Φ ⟨Herr, %v, Hl⟩ HΦ
  unfold prog
  wp_store
  imod ghost_var_alloc false with ⟨%γ, Hauth, Hfrag⟩
  imod CancelableInvariant.alloc ⊤ nroot
      iprop(l ↦ LitV (LitInt 0) ∗ own_auth γ true ∨ l ↦ LitV (LitInt (-1)) ∗ own_auth γ false)
      $$ [Hl Hauth] with ⟨%γ1, #I, Hc⟩
  · inext
    iright
    iframe
  wp_pures
  ihave ⟨Hc, Hc'⟩ := (cinv_own_halves γ1).mp $$ Hc
  iapply pgl_wp_fupd
  wp_apply wp_par' (fun _ => iprop(own_frag γ true ∗ CancelableInvariant.own γ1 (1 : Qp).half))
    (fun _ => iprop(CancelableInvariant.own γ1 (1 : Qp).half)) $$ [Herr Hfrag Hc] [Hc']
  · wp_apply wp_flip_adv ⊤ _ (fun x => if x then 0 else 1) (by norm_num) $$ Herr with %b Herr
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iexfalso
      iapply ErrorCredit.contradict le_rfl $$ Herr
    wp_pures
    imod acc_strong ⊤ nroot γ1 _ _ CoPset.subseteq_top $$ I Hc with ⟨K, Hc, Hclose⟩
    icases K with >(⟨H, Hauth⟩ | ⟨H, Hauth⟩)
    · ihave %K := ghost_var_agree $$ Hauth Hfrag
      cases K
    · wp_store
      imod ghost_var_update γ true _ _ $$ Hauth Hfrag with ⟨Hauth, Hfrag⟩
      imod Hclose $$ %_ [H Hauth]
      · ileft
        inext
        ileft
        iframe
      rw [LawfulSet.subset_union_diff CoPset.subseteq_top]
      imodintro
      iframe
  · iloeb as IH generalizing Hc'
    wp_bind (Load _)
    imod acc_strong ⊤ nroot γ1 _ _ CoPset.subseteq_top $$ I Hc' with ⟨K, Hc, Hclose⟩
    icases K with >(⟨H, Hauth⟩ | ⟨H, Hauth⟩)
    · wp_load
      imod Hclose $$ %_ [H Hauth]
      · ileft
        inext
        ileft
        iframe
      rw [LawfulSet.subset_union_diff CoPset.subseteq_top]
      imodintro
      wp_pures
      iexact Hc
    · wp_load
      imod Hclose $$ %_ [H Hauth]
      · ileft
        inext
        iright
        iframe
      rw [LawfulSet.subset_union_diff CoPset.subseteq_top]
      imodintro
      wp_pures
      iapply IH $$ Hc
  · iintro %v1 %v2 ⟨⟨Hfrag, Hc⟩, Hc'⟩
    ihave Hc := (cinv_own_halves γ1).mpr $$ [Hc Hc']
    · iframe
    inext
    imod cancel ⊤ CoPset.subseteq_top $$ I Hc with H
    icases H with >(⟨H, Hauth⟩ | ⟨H, Hauth⟩)
    · imodintro
      iapply HΦ $$ H
    · ihave %K := ghost_var_agree $$ Hauth Hfrag
      cases K

end proof

end Coneris.Examples.MessagePass
