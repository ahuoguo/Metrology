module

public import Metrology.Foxtrot.ProofMode

/-!
# Coupling rules with error credits for Foxtrot

Ported from clutch/theories/foxtrot/error_rules.v

## Rocq → Lean map
* `tp_rand_r_err` ↦ `tp_rand_r_err` (same argument order `N z E K j m`, with the Rocq
  `TCEq N (Z.to_nat z)` premise as an explicit equality `(hN : N = z.toNat)`).

## Design choices / deviations
* Errors are `ℝ≥0∞`; Rocq's `/ (N + 1)%nat` is `((N + 1 : ℕ) : ℝ≥0∞)⁻¹`, and the positivity
  side condition `0 <= / (N + 1)` vanishes.
* Rocq's `ec_supply_ec_inv` (splitting the supply as `x + x'`) is replaced by
  `ErrorCredit.supply_bound` (`ε ≤ ε1`) and `ErrorCredit.supply_decrease`, which leaves the
  supply `ε1 - ε`; the continuation of `spec_coupl_step_r` is run with error `ε1 - ε`.
* The `pgl` obligation (Rocq: `fill_dmap`, `head_prim_step_eq`, `pgl_dbind`,
  `ub_unif_err_nat`) is proved via the helper `prim_step_fill_head` of
  `Foxtrot.PrimitiveLaws`, `pgl_dbind`, `pgl_dret` and `ub_unif_err_nat`.
* Rocq `rand #z` is `Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))`, `#n` for `n : nat` is
  `Val (LitV (LitInt (n : ℤ)))`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

section rules

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `tp_rand_r_err`. Spec `rand`: sampling on the right avoids a chosen value `m`, at the
cost of `1 / (N + 1)` error credits. -/
theorem tp_rand_r_err (N : ℕ) (z : ℤ) (E : CoPset) (K : List ectx_item) (j m : ℕ)
    (hN : N = z.toNat) :
    j ⤇ fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) ⊢@{IProp GF}
      ↯ (((N + 1 : ℕ) : ℝ≥0∞)⁻¹) -∗
      pupd E E iprop(∃ n : ℕ, ⌜n ≤ N⌝ ∗ ⌜n ≠ m⌝ ∗
        j ⤇ fill K (Val (LitV (LitInt (n : ℤ))))) := by
  subst hN
  have hε : 1 / ((z.toNat : ℝ≥0∞) + 1) = ((z.toNat + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [one_div]
    push_cast
    rfl
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq, foxtrotGS_err_interp_eq]
  iintro Hj Herr %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  ihave %Hle := ErrorCredit.supply_bound $$ Hε Herr
  have Hhead : head_step (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ =
      dmap (fun n : Fin (z.toNat + 1) => ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) :
        expr × state × List expr)) (dunifP z.toNat) := rfl
  have Hstep := prim_step_fill_head K _ σ _ _ Hhead (dunifP_mass _)
  have Hred : reducible (Λ := con_prob_lang)
      (fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit)))) σ := by
    obtain ⟨a, ha⟩ := exists_pos_of_mass_one _ (dunifP_mass z.toNat)
    exact ⟨_, by rw [Hstep, dmap_pos]; exact ⟨a, rfl, ha⟩⟩
  let R : expr × state × List expr → Prop := fun p =>
    ∃ m' : ℕ, p = (fill K (Val (LitV (LitInt (m' : ℤ)))), σ, []) ∧ m' ≠ m ∧ m' ≤ z.toNat
  have Hpgl : pgl (prim_step (Λ := con_prob_lang)
      (fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit)))) σ)
      (fun p => R p ∧ p.2.1.tapes = σ.tapes) (((z.toNat + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
    rw [Hstep, dmap, ← hε, ← add_zero (1 / ((z.toNat : ℝ≥0∞) + 1))]
    refine pgl_dbind _ _ (fun x : Fin (z.toNat + 1) => (x : ℕ) ≠ m) _ _ _
      (fun a ha => pgl_dret _ _ ⟨⟨a, rfl, ha, Nat.lt_succ_iff.1 a.2⟩, rfl⟩)
      (ub_unif_err_nat _ m)
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r R _ σ.tapes (ε1 - ((z.toNat + 1 : ℕ) : ℝ≥0∞)⁻¹) ((es, σ) : CPState)
    σ1 _ ε1 j _ Hred Hsome (by rw [add_tsub_cancel_of_le Hle]) Hpgl
  iintro %e' %σ' %efs %⟨⟨m', Heq, Hne, Hle'⟩, -⟩
  obtain ⟨rfl, h2⟩ := Prod.mk.inj Heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
  imod ErrorCredit.supply_decrease $$ Hε Herr with Hε
  imod spec_update_prog _ _ j _ (fill K (Val (LitV (LitInt (m' : ℤ))))) $$ Hs Hj with ⟨Hs, Hj⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe Hσ Hs Hε
  iexists m'
  iframe Hj
  isplit
  · ipureintro
    exact Hle'
  · ipureintro
    exact Hne

end rules

end Foxtrot
