module

public import Metrology.Coneris.PrimitiveLaws
public import Metrology.Coneris.WpUpdate
public import Metrology.Coneris.ProofMode

/-!
# Coneris error bound rules

Ported from clutch/theories/coneris/error_rules.v

Rules that spend error credits `↯ ε` at a `rand` (`wp_rand_err*`, the advanced composition
`wp_couple_rand_adv_comp*`), and rules that presample onto tapes while redistributing error
credits (`wp_presample*`, `wp_update_presample*`, `state_update_presample*`).

## Design choices (Rocq → Lean)

* Errors are `ℝ≥0∞` (Rocq: `R`/`nonnegreal`). The hypotheses `0 <= ε2 n`, `0 <= εI`, ... are
  dropped, and the boundedness side conditions `∃ r, ∀ ρ, ε2 ρ ≤ r` are discharged with `⊤`.
  `/ (N + 1)` is `((N : ℝ≥0∞) + 1)⁻¹` and `1 / S N` is `1 / ((N : ℝ≥0∞) + 1)`. `SeriesC` is `∑'`.
* `TCEq N (Z.to_nat z)` is a plain hypothesis `(hN : N = z.toNat)`. `rand #z` is
  `Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))` and `#n` for `n : fin (S N)` is
  `LitV (LitInt ((n : ℕ) : ℤ))`, as in `Coneris.PrimitiveLaws`.
* `Forall P l` is `∀ m ∈ l, P m`. `seq 0 (S N)` is `List.range (N + 1)`. `gset nat` is
  `Finset ℕ` and `size` is `Finset.card`. In `wp_rand_err_set_in_out` and
  `state_step_err_set_in_out`, `N + 1 - size ns` is the truncated `ℝ≥0∞` subtraction. It agrees
  with Rocq because `size ns ≤ N + 1` follows from the `Hlen` hypothesis.
* `ns' ∈ enum_uniform_fin_list N p` is `ns'.length = p`, which is Rocq's
  `elem_of_enum_uniform_fin_list`; `enum_uniform_fin_list` is not ported. `(length n =? p)` is
  `n.length = p`.
* The WP variables `s`, `E`, `e` and `Φ` are implicit. `wp_rand_err` and `wp_rand_err_nat` take
  any stuckness `s`; the other rules use the NotStuck `WP e @ E {{ Φ }}`, as in Rocq. The Texan
  triples use iris-lean's double braces, as in `Coneris.PrimitiveLaws`.
* The single-draw ε2 continuations are `(partial_inv_fun f ρ).elim 0 ε2` (Rocq: a `match` on
  the configuration, or `epsilon` of the classical witness), where `f` is the injective map
  from samples to configurations or states.

## Proofs that differ from Rocq
* The four `wp_rand_err*` rules and the `pgl_rand_*` lemmas are instances of the helpers
  `wp_rand_err_pgl` and `pgl_rand_of_unif` (Rocq repeats the same proof four times).
* `state_step_coupl_state_adv_comp_con_prob_lang` is proved directly from
  `state_step_coupl_state_adv_comp` rather than through the `iterM` version with `p = 1`.
* `wp_presample`, `wp_presample_adv_comp` and `state_update_presample_exp` share one proof,
  `state_update_presample_exp_aux`. It is stated before `wp_presample` so that the WP rules
  follow from it via `imod`, which avoids unfolding the WP.
* `wp_couple_rand_adv_comp1'` weakens `↯ ε1` to `↯ (∑' ..)`. Rocq instead adds the difference to
  `ε2`, which is not needed in `ℝ≥0∞`.
* `wp_couple_rand_adv_comp1` is `wp_couple_rand_adv_comp`, since boundedness is trivial.

## Omitted
* `match_nonneg_coercions`: `NNRbar` plumbing with no `ℝ≥0∞` content.
* The `#[local]` helpers `Rmax_seq`, `le_Rmax_seq` and `fin_function_bounded`. They are only used
  for the (trivial) boundedness of `ε2`; `Prob.fin_function_bounded` exists anyway.

## Added helpers (not in Rocq)
`pgl_dmap` (belongs in `Prob`), `prim_step_rand`, `pgl_rand_of_unif`, `N_succ_mul_inv`,
`wp_rand_err_pgl`, `SeriesC_unif_le`, `SeriesC_fin_in_list_le`, `SeriesC_in_out_le`,
`mem_get_active_of_lookup`, `state_update_presample_exp_aux`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris

/-! ## Metatheory -/

section metatheory

/-- Helper: `pgl` is preserved by `dmap`. -/
theorem pgl_dmap {A B : Type*} [Countable A] [Countable B] (f : A → B) (μ : Distr A)
    (P : A → Prop) (Q : B → Prop) (ε : ℝ≥0∞) (hPQ : ∀ a, P a → Q (f a)) (h : pgl μ P ε) :
    pgl (dmap f μ) Q ε := by
  have := pgl_dbind (fun a => dret (f a)) μ P Q ε 0 (fun a ha => pgl_dret _ _ (hPQ a ha)) h
  simpa [dmap] using this

/-- Helper: the distribution of `rand #z`. -/
theorem prim_step_rand (z : ℤ) (σ1 : state) :
    prim_step (Λ := con_prob_lang) (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ1 =
      dmap (fun n : Fin (z.toNat + 1) =>
        (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, ([] : List expr))) (dunifP z.toNat) := by
  rw [prim_step_eq_head_step _ _ ⟨_, _, _, head_step_rel.RandNoTapeS z z.toNat 0 σ1 rfl⟩]
  rfl

/-- Helper: any `pgl` of the uniform distribution transfers to `rand #z`. -/
theorem pgl_rand_of_unif (N : ℕ) (z : ℤ) (σ1 : state) (hN : N = z.toNat)
    (P : Fin (N + 1) → Prop) (ε : ℝ≥0∞) (h : pgl (dunifP N) P ε) :
    pgl (prim_step (Λ := con_prob_lang) (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ1)
      (fun ρ => ∃ n : Fin (N + 1), P n ∧ ρ = (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, [])) ε := by
  subst hN
  rw [prim_step_rand]
  exact pgl_dmap _ _ P _ ε (fun n hn => ⟨n, hn, rfl⟩) h

/-- Rocq: `pgl_rand_trivial`. -/
theorem pgl_rand_trivial (N : ℕ) (z : ℤ) (σ1 : state) (hN : N = z.toNat) :
    pgl (prim_step (Λ := con_prob_lang) (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ1)
      (fun ρ => ∃ n : Fin (N + 1), ρ = (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, [])) 0 :=
  pgl_mon_pred _ _ _ _ (fun _ ⟨n, _, h⟩ => ⟨n, h⟩)
    (pgl_rand_of_unif N z σ1 hN (fun _ => True) 0 (pgl_trivial _ 0))

/-- Rocq: `pgl_rand_err`. -/
theorem pgl_rand_err (N : ℕ) (z : ℤ) (σ1 : state) (m : Fin (N + 1)) (hN : N = z.toNat) :
    pgl (prim_step (Λ := con_prob_lang) (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ1)
      (fun ρ => ∃ n : Fin (N + 1), n ≠ m ∧ ρ = (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, []))
      (1 / ((N : ℝ≥0∞) + 1)) :=
  pgl_rand_of_unif N z σ1 hN _ _ (ub_unif_err N m)

/-- Rocq: `pgl_rand_err_nat`. Same lemma for `m` an arbitrary natural. -/
theorem pgl_rand_err_nat (N : ℕ) (z : ℤ) (σ1 : state) (m : ℕ) (hN : N = z.toNat) :
    pgl (prim_step (Λ := con_prob_lang) (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ1)
      (fun ρ => ∃ n : Fin (N + 1), (n : ℕ) ≠ m ∧
        ρ = (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, []))
      (1 / ((N : ℝ≥0∞) + 1)) :=
  pgl_rand_of_unif N z σ1 hN _ _ (ub_unif_err_nat N m)

/-- Rocq: `pgl_rand_err_list_nat`. Generalization to lists. -/
theorem pgl_rand_err_list_nat (N : ℕ) (z : ℤ) (σ1 : state) (ms : List ℕ) (hN : N = z.toNat) :
    pgl (prim_step (Λ := con_prob_lang) (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ1)
      (fun ρ => ∃ n : Fin (N + 1), (∀ m ∈ ms, (n : ℕ) ≠ m) ∧
        ρ = (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, []))
      ((ms.length : ℝ≥0∞) / ((N : ℝ≥0∞) + 1)) :=
  pgl_rand_of_unif N z σ1 hN _ _ (ub_unif_err_list_nat N ms)

/-- Rocq: `pgl_rand_err_list_int`. -/
theorem pgl_rand_err_list_int (N : ℕ) (z : ℤ) (σ1 : state) (ms : List ℤ) (hN : N = z.toNat) :
    pgl (prim_step (Λ := con_prob_lang) (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ1)
      (fun ρ => ∃ n : Fin (N + 1), (∀ m ∈ ms, ((n : ℕ) : ℤ) ≠ m) ∧
        ρ = (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, []))
      ((ms.length : ℝ≥0∞) / ((N : ℝ≥0∞) + 1)) :=
  pgl_rand_of_unif N z σ1 hN _ _ (ub_unif_err_list_int N ms)

/-- Helper: `(N + 1) * (1 / (N + 1)) = 1` in `ℝ≥0∞`. -/
theorem N_succ_mul_inv (N : ℕ) : ((N : ℝ≥0∞) + 1) * (1 / ((N : ℝ≥0∞) + 1)) = 1 := by
  rw [one_div]
  exact ENNReal.mul_inv_cancel (by positivity) (by simp)

end metatheory

/-! ## Rules -/

section rules

variable {GF : BundledGFunctors} [conerisGS GF]
variable {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}

/-- Helper: the common proof of the `wp_rand_err*` rules: spend `↯ ε` to avoid the outcomes of
`rand #z` outside `P`, where `P` fails with probability at most `ε` under `dunifP N`. -/
theorem wp_rand_err_pgl (N : ℕ) (z : ℤ) (P : Fin (N + 1) → Prop) (ε : ℝ≥0∞)
    (hN : N = z.toNat) (Hpgl : pgl (dunifP N) P ε) :
    ↯ ε ∗ (∀ x : Fin (N + 1), ⌜P x⌝ -∗ Φ (LitV (LitInt ((x : ℕ) : ℤ))))
      ⊢ WP (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ s; E {{ Φ }} := by
  iintro ⟨Herr, Hwp⟩
  iapply wp_lift_step_fupd_glm
  iintro %σ1 %ε1 ⟨Hσ, Hε⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  simp only [conerisGS_err_interp_eq]
  ihave %Hle := ErrorCredit.supply_bound $$ Hε Herr
  iapply state_step_coupl_ret
  simp only [con_prob_lang.to_val]
  iapply prog_coupl_prim_step
  · iintro !> %e2 %σ2 %efs !>
    iapply state_step_coupl_ret_err_ge_1 _ _ _ le_rfl
  iexists (fun ρ => ∃ n : Fin (N + 1), P n ∧ ρ = (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, [])),
    ε, ε1 - ε
  isplitr
  · ipureintro
    exact reducible_of_rel (head_step_rel.RandNoTapeS z z.toNat 0 σ1 rfl)
  isplitr
  · ipureintro
    rw [add_tsub_cancel_of_le Hle]
  isplitr
  · ipureintro
    exact pgl_rand_of_unif N z σ1 hN P ε Hpgl
  iintro %e2 %σ2 %efs %⟨n, Hn, Heq⟩
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl, rfl⟩ := Heq
  imod ErrorCredit.supply_decrease $$ Hε Herr with Hε
  iintro !> !>
  iapply state_step_coupl_ret
  imod Hclose
  imodintro
  iframe Hσ Hε
  isplitl
  · iapply pgl_wp_value'
    iapply Hwp $$ %n %Hn
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_rand_err`. -/
theorem wp_rand_err (N : ℕ) (z : ℤ) (m : Fin (N + 1)) (hN : N = z.toNat) :
    ↯ ((N : ℝ≥0∞) + 1)⁻¹ ∗ (∀ x : Fin (N + 1), ⌜x ≠ m⌝ -∗ Φ (LitV (LitInt ((x : ℕ) : ℤ))))
      ⊢ WP (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ s; E {{ Φ }} := by
  have h := ub_unif_err N m
  rw [one_div] at h
  exact wp_rand_err_pgl N z _ _ hN h

/-- Rocq: `wp_rand_err_nat`. -/
theorem wp_rand_err_nat (N : ℕ) (z : ℤ) (m : ℕ) (hN : N = z.toNat) :
    ↯ ((N : ℝ≥0∞) + 1)⁻¹ ∗
      (∀ x : Fin (N + 1), ⌜(x : ℕ) ≠ m⌝ -∗ Φ (LitV (LitInt ((x : ℕ) : ℤ))))
      ⊢ WP (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ s; E {{ Φ }} := by
  have h := ub_unif_err_nat N m
  rw [one_div] at h
  exact wp_rand_err_pgl N z _ _ hN h

/-- Rocq: `wp_rand_err_list_nat`. -/
theorem wp_rand_err_list_nat (N : ℕ) (z : ℤ) (ns : List ℕ) (hN : N = z.toNat) :
    ↯ ((ns.length : ℝ≥0∞) / ((N : ℝ≥0∞) + 1)) ∗
      (∀ x : Fin (N + 1), ⌜∀ m ∈ ns, (x : ℕ) ≠ m⌝ -∗ Φ (LitV (LitInt ((x : ℕ) : ℤ))))
      ⊢ WP (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ E {{ Φ }} :=
  wp_rand_err_pgl N z _ _ hN (ub_unif_err_list_nat N ns)

/-- Rocq: `wp_rand_err_list_int`. -/
theorem wp_rand_err_list_int (N : ℕ) (z : ℤ) (zs : List ℤ) (hN : N = z.toNat) :
    ↯ ((zs.length : ℝ≥0∞) / ((N : ℝ≥0∞) + 1)) ∗
      (∀ x : Fin (N + 1), ⌜∀ m ∈ zs, ((x : ℕ) : ℤ) ≠ m⌝ -∗ Φ (LitV (LitInt ((x : ℕ) : ℤ))))
      ⊢ WP (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ E {{ Φ }} :=
  wp_rand_err_pgl N z _ _ hN (ub_unif_err_list_int N zs)

/-- Rocq: `wp_rand_err_filter`. -/
theorem wp_rand_err_filter (N : ℕ) (z : ℤ) (P : ℕ → Bool) (hN : N = z.toNat) :
    ↯ (((List.range (N + 1)).filter P).length / ((N : ℝ≥0∞) + 1)) ∗
      (∀ x : Fin (N + 1), ⌜P x = false⌝ -∗ Φ (LitV (LitInt ((x : ℕ) : ℤ))))
      ⊢ WP (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ E {{ Φ }} := by
  iintro ⟨H1, H2⟩
  iapply wp_rand_err_list_nat N z ((List.range (N + 1)).filter P) hN
  iframe H1
  iintro %x %H0
  iapply H2
  ipureintro
  cases HPx : P x
  · rfl
  · exact absurd rfl (H0 x (List.mem_filter.2 ⟨List.mem_range.2 x.2, HPx⟩))

/-- Rocq: `mean_constraint_ub`. -/
theorem mean_constraint_ub (N : ℕ) (ε1 : ℝ≥0∞) (ε2 : Fin (N + 1) → ℝ≥0∞)
    (Hsum : ∑' n, 1 / ((N : ℝ≥0∞) + 1) * ε2 n = ε1) : ∃ r, 0 ≤ r ∧ ∀ n, ε2 n ≤ r := by
  refine ⟨((N : ℝ≥0∞) + 1) * ε1, zero_le, fun n => ?_⟩
  rw [← Hsum]
  calc ε2 n = ((N : ℝ≥0∞) + 1) * (1 / ((N : ℝ≥0∞) + 1) * ε2 n) := by
        rw [← mul_assoc, N_succ_mul_inv, one_mul]
    _ ≤ _ := mul_le_mul_right (ENNReal.le_tsum (f := fun n => 1 / ((N : ℝ≥0∞) + 1) * ε2 n) n) _

/-- Rocq: `wp_couple_rand_adv_comp`. -/
theorem wp_couple_rand_adv_comp (N : ℕ) (z : ℤ) (ε1 : ℝ≥0∞) (ε2 : Fin (N + 1) → ℝ≥0∞)
    (hN : N = z.toNat) (Hε1 : ∑' n, 1 / ((N : ℝ≥0∞) + 1) * ε2 n = ε1) :
    {{ ↯ ε1 }} (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ E
    {{ (n : Fin (N + 1)), RET LitV (LitInt ((n : ℕ) : ℤ)); (↯ (ε2 n) : IProp GF) }} := by
  subst hN
  iintro %Ψ Herr HΨ
  iapply wp_lift_step_fupd_glm
  iintro %σ1 %ε_now ⟨Hσ, Hε⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  simp only [conerisGS_err_interp_eq]
  ihave %Hle := ErrorCredit.supply_bound $$ Hε Herr
  iapply state_step_coupl_ret
  simp only [con_prob_lang.to_val]
  iapply prog_coupl_adv_comp
  · iintro !> %e2 %σ2 %efs !>
    iapply state_step_coupl_ret_err_ge_1 _ _ _ le_rfl
  let f : Fin (z.toNat + 1) → expr × state × List expr :=
    fun n => (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, [])
  have hf : Function.Injective f := by
    intro a b h
    simp only [f, Prod.mk.injEq, expr.Val.injEq, val.LitV.injEq, base_lit.LitInt.injEq,
      Nat.cast_inj, and_true] at h
    exact Fin.ext h
  iexists (fun ρ => ∃ n, ρ = f n), 0,
    (fun ρ => (ε_now - ε1) + (partial_inv_fun f ρ).elim 0 ε2)
  isplitr
  · ipureintro
    exact reducible_of_rel (head_step_rel.RandNoTapeS z z.toNat 0 σ1 rfl)
  isplitr
  · ipureintro
    exact ⟨⊤, fun _ => le_top⟩
  isplitr
  · ipureintro
    rw [zero_add, prim_step_rand, Expval_dmap]
    have hc : ∀ n, (partial_inv_fun f (f n)).elim 0 ε2 = ε2 n := fun n => by
      rw [partial_inv_fun_inj hf]; rfl
    simp only [Function.comp_def]
    rw [show (fun n => ε_now - ε1 + (partial_inv_fun f (f n)).elim 0 ε2) =
        fun n => ε_now - ε1 + ε2 n from funext fun n => by rw [hc]]
    rw [Expval_plus, Expval_const, dunifP_mass, mul_one]
    have : Expval (dunifP z.toNat) ε2 = ε1 := by
      rw [← Hε1]
      unfold Expval
      congr 1
      funext n
      rw [dunifP_pmf, one_div]
      push_cast
      rfl
    rw [this, tsub_add_cancel_of_le Hle]
  isplitr
  · ipureintro
    exact pgl_rand_trivial _ z σ1 rfl
  iintro %e2 %σ2 %efs %⟨n, Heq⟩
  have hp : partial_inv_fun f (e2, σ2, efs) = some n := by rw [Heq]; exact partial_inv_fun_inj hf n
  simp only [f, Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl, rfl⟩ := Heq
  simp only [hp, Option.elim]
  imod ErrorCredit.supply_decrease $$ Hε Herr with Hε
  imodintro
  inext
  by_cases hlt : ε_now - ε1 + ε2 n < 1
  · iapply state_step_coupl_ret
    imod ErrorCredit.supply_increase hlt $$ Hε with ⟨Hε, Herr⟩
    imod Hclose
    imodintro
    iframe Hσ Hε
    isplitl
    · iapply pgl_wp_value'
      iapply HΨ $$ Herr
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  · iapply state_step_coupl_ret_err_ge_1 _ _ _ (not_lt.1 hlt)

/-- Rocq: `wp_couple_rand_adv_comp1`. (In `ℝ≥0∞` it is `wp_couple_rand_adv_comp`: the Rocq
proof only derives the boundedness of `ε2` from `mean_constraint_ub`.) -/
theorem wp_couple_rand_adv_comp1 (N : ℕ) (z : ℤ) (ε1 : ℝ≥0∞) (ε2 : Fin (N + 1) → ℝ≥0∞)
    (hN : N = z.toNat) (Hε1 : ∑' n, 1 / ((N : ℝ≥0∞) + 1) * ε2 n = ε1) :
    {{ ↯ ε1 }} (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ E
    {{ (n : Fin (N + 1)), RET LitV (LitInt ((n : ℕ) : ℤ)); (↯ (ε2 n) : IProp GF) }} := by
  obtain ⟨_, _, _⟩ := mean_constraint_ub N ε1 ε2 Hε1
  exact wp_couple_rand_adv_comp N z ε1 ε2 hN Hε1

/-- Rocq: `wp_couple_rand_adv_comp1'`. -/
theorem wp_couple_rand_adv_comp1' (N : ℕ) (z : ℤ) (ε1 : ℝ≥0∞) (ε2 : Fin (N + 1) → ℝ≥0∞)
    (hN : N = z.toNat) (Hε1 : ∑' n, 1 / ((N : ℝ≥0∞) + 1) * ε2 n ≤ ε1) :
    {{ ↯ ε1 }} (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ E
    {{ (n : Fin (N + 1)), RET LitV (LitInt ((n : ℕ) : ℤ)); (↯ (ε2 n) : IProp GF) }} := by
  iintro %Ψ Herr HΨ
  iapply wp_couple_rand_adv_comp1 N z _ ε2 hN rfl $$ %Ψ [Herr] HΨ
  iapply ErrorCredit.weaken Hε1 $$ Herr

/-- Helper: a sum over `Fin (N + 1)` weighted by `1 / (N + 1)` is bounded by `ε` as soon as the
unweighted sum is bounded by `ε * (N + 1)`. -/
theorem SeriesC_unif_le (N : ℕ) (f : Fin (N + 1) → ℝ≥0∞) (ε : ℝ≥0∞)
    (h : ∑' x, f x ≤ ε * ((N : ℝ≥0∞) + 1)) : ∑' x, 1 / ((N : ℝ≥0∞) + 1) * f x ≤ ε := by
  rw [ENNReal.tsum_mul_left]
  calc 1 / ((N : ℝ≥0∞) + 1) * ∑' x, f x ≤ 1 / ((N : ℝ≥0∞) + 1) * (ε * ((N : ℝ≥0∞) + 1)) :=
        mul_le_mul_right h _
    _ = ε * (((N : ℝ≥0∞) + 1) * (1 / ((N : ℝ≥0∞) + 1))) := by ring
    _ = ε := by rw [N_succ_mul_inv, mul_one]

/-- Helper: at most `ns.length` elements of `Fin (N + 1)` belong to the list `ns`. -/
theorem SeriesC_fin_in_list_le (N : ℕ) (ns : List ℕ) :
    ∑' x : Fin (N + 1), (if (x : ℕ) ∈ ns then (1 : ℝ≥0∞) else 0) ≤ ns.length := by
  classical
  have := SeriesC_fin_in_set N (ns.toFinset.filter (· < N + 1)) (fun x hx => (Finset.mem_filter.1 hx).2)
  rw [show (fun x : Fin (N + 1) => if (x : ℕ) ∈ ns then (1 : ℝ≥0∞) else 0) =
      fun x : Fin (N + 1) => if (x : ℕ) ∈ ns.toFinset.filter (· < N + 1) then (1 : ℝ≥0∞) else 0
    from funext fun x => by simp [Nat.lt_succ_iff.1 x.2], this]
  exact_mod_cast (Finset.card_filter_le _ _).trans (List.toFinset_card_le ns)

/-- Rocq: `wp_rand_err_list_adv`. -/
theorem wp_rand_err_list_adv (N : ℕ) (z : ℤ) (ns : List ℕ) (ε0 ε1 : ℝ≥0∞) (hN : N = z.toNat)
    (Hleq : ε1 * ns.length ≤ ε0 * ((N : ℝ≥0∞) + 1)) :
    ↯ ε0 ∗ (∀ x : Fin (N + 1),
        (⌜∀ m ∈ ns, (x : ℕ) ≠ m⌝ ∨ ↯ ε1) -∗ Φ (LitV (LitInt ((x : ℕ) : ℤ))))
      ⊢ WP (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ E {{ Φ }} := by
  classical
  have Hsum : ∑' x : Fin (N + 1), 1 / ((N : ℝ≥0∞) + 1) * (if (x : ℕ) ∈ ns then ε1 else 0) ≤ ε0 := by
    refine SeriesC_unif_le N _ ε0 (le_trans ?_ Hleq)
    rw [show (fun x : Fin (N + 1) => if (x : ℕ) ∈ ns then ε1 else 0) =
        fun x : Fin (N + 1) => ε1 * (if (x : ℕ) ∈ ns then 1 else 0) from
      funext fun x => by split_ifs <;> simp, ENNReal.tsum_mul_left]
    exact mul_le_mul_right (SeriesC_fin_in_list_le N ns) _
  iintro ⟨Herr, Hwp⟩
  iapply wp_couple_rand_adv_comp1' N z ε0 (fun x => if (x : ℕ) ∈ ns then ε1 else 0) hN Hsum
    $$ %Φ Herr
  iintro !> %n Hn
  by_cases h : (n : ℕ) ∈ ns
  · simp only [h, ite_true]
    iapply Hwp
    iright
    iexact Hn
  · iapply Hwp
    ileft
    ipureintro
    intro m hm heq
    exact h (heq ▸ hm)

/-- Helper: the expected error of the `set_in_out` rules. -/
theorem SeriesC_in_out_le (N : ℕ) (ns : Finset ℕ) (ε εI εO : ℝ≥0∞) (Hlen : ∀ n ∈ ns, n < N + 1)
    (Hleq : εI * ns.card + εO * ((N : ℝ≥0∞) + 1 - ns.card) ≤ ε * ((N : ℝ≥0∞) + 1)) :
    ∑' x : Fin (N + 1), 1 / ((N : ℝ≥0∞) + 1) * (if (x : ℕ) ∈ ns then εI else εO) ≤ ε := by
  refine SeriesC_unif_le N _ ε (le_trans (le_of_eq ?_) Hleq)
  rw [show (fun x : Fin (N + 1) => if (x : ℕ) ∈ ns then εI else εO) =
      fun x : Fin (N + 1) => εI * (if (x : ℕ) ∈ ns then 1 else 0) +
        εO * (if (x : ℕ) ∉ ns then 1 else 0) from
    funext fun x => by by_cases h : (x : ℕ) ∈ ns <;> simp [h],
    ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    SeriesC_fin_in_set N ns Hlen, SeriesC_fin_not_in_set N ns Hlen]

/-- Rocq: `wp_rand_err_set_in_out` (Rocq's `gset nat` is a `Finset ℕ`). -/
theorem wp_rand_err_set_in_out (N : ℕ) (z : ℤ) (ns : Finset ℕ) (ε εI εO : ℝ≥0∞)
    (hN : N = z.toNat) (Hlen : ∀ n ∈ ns, n < N + 1)
    (Hleq : εI * ns.card + εO * ((N : ℝ≥0∞) + 1 - ns.card) ≤ ε * ((N : ℝ≥0∞) + 1)) :
    ↯ ε ∗ (∀ x : Fin (N + 1),
        ((⌜(x : ℕ) ∉ ns⌝ ∗ ↯ εO) ∨ (⌜(x : ℕ) ∈ ns⌝ ∗ ↯ εI)) -∗
          Φ (LitV (LitInt ((x : ℕ) : ℤ))))
      ⊢ WP (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ E {{ Φ }} := by
  have Hsum := SeriesC_in_out_le N ns ε εI εO Hlen Hleq
  iintro ⟨Herr, Hwp⟩
  iapply wp_couple_rand_adv_comp1' N z ε (fun x => if (x : ℕ) ∈ ns then εI else εO) hN Hsum
    $$ %Φ Herr
  iintro !> %n Hn
  by_cases h : (n : ℕ) ∈ ns
  · simp only [h, ite_true]
    iapply Hwp
    iright
    iframe Hn
    ipureintro
    exact h
  · simp only [h, ite_false]
    iapply Hwp
    ileft
    iframe Hn
    ipureintro
    exact h

/-- Rocq: `wp_rand_err_filter_adv`. -/
theorem wp_rand_err_filter_adv (N : ℕ) (z : ℤ) (P : ℕ → Bool) (ε0 ε1 : ℝ≥0∞)
    (hN : N = z.toNat)
    (HK : ε1 * ((List.range (N + 1)).filter P).length ≤ ε0 * ((N : ℝ≥0∞) + 1)) :
    ↯ ε0 ∗ (∀ x : Fin (N + 1), (⌜P x = false⌝ ∨ ↯ ε1) -∗ Φ (LitV (LitInt ((x : ℕ) : ℤ))))
      ⊢ WP (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ E {{ Φ }} := by
  iintro ⟨H1, Hwp⟩
  iapply wp_rand_err_list_adv N z ((List.range (N + 1)).filter P) ε0 ε1 hN HK
  iframe H1
  iintro %x (%Hfor | Herr)
  · iapply Hwp
    ileft
    ipureintro
    cases HPx : P x
    · rfl
    · exact absurd rfl (Hfor x (List.mem_filter.2 ⟨List.mem_range.2 x.2, HPx⟩))
  · iapply Hwp
    iright
    iexact Herr

/-- Rocq: `pgl_state`. -/
theorem pgl_state (N : ℕ) (σ : state) (α : Loc) (ns : List (Fin (N + 1)))
    (h : σ.tapes[α]? = some ⟨N, ns⟩) :
    pgl (con_prob_lang.state_step σ α)
      (fun σ' => ∃ n : Fin (N + 1), σ' = state_upd_tapes (·.insert α ⟨N, ns ++ [n]⟩) σ) 0 := by
  rw [state_step_unfold σ α N ns h]
  exact pgl_dmap _ _ (fun _ => True) _ 0 (fun n _ => ⟨n, rfl⟩) (pgl_trivial _ 0)

/-- Rocq: `pgl_iterM_state`. Rocq's `ns' ∈ enum_uniform_fin_list N p` is `ns'.length = p`
(Rocq: `elem_of_enum_uniform_fin_list`). -/
theorem pgl_iterM_state (N p : ℕ) (σ : state) (α : Loc) (ns : List (Fin (N + 1)))
    (h : σ.tapes[α]? = some ⟨N, ns⟩) :
    pgl (iterM p (fun σ => con_prob_lang.state_step σ α) σ)
      (fun σ' => ∃ ns' : List (Fin (N + 1)),
        ns'.length = p ∧ σ' = state_upd_tapes (·.insert α ⟨N, ns ++ ns'⟩) σ) 0 := by
  rw [iterM_state_step_unfold σ N p α ns h]
  refine pgl_dmap _ _ (fun v => v.length = p) _ 0 (fun v hv => ⟨v, hv, rfl⟩) ?_
  classical
  rw [pgl_unfold]
  refine le_of_eq (ENNReal.tsum_eq_zero.2 fun v => ?_)
  by_cases hv : v.length = p <;> simp [hv, dunifv_pmf]

/-- Helper: a tape that `σ.tapes` maps is active. -/
theorem mem_get_active_of_lookup (σ : state) (α : Loc) (t : tape) (h : σ.tapes[α]? = some t) :
    α ∈ get_active σ :=
  Std.ExtTreeMap.mem_keys.2 (Std.ExtTreeMap.mem_iff_isSome_getElem?.2 (by simp [h]))

/-- Rocq: `state_step_coupl_iterM_state_adv_comp_con_prob_lang`. Rocq's `(length n =? p)` is
`n.length = p`, and `1 / (S N) ^ p` is `1 / (N + 1) ^ p`. -/
theorem state_step_coupl_iterM_state_adv_comp_con_prob_lang (p : ℕ) (α : Loc) (σ1 : state)
    (Z : state → ℝ≥0∞ → IProp GF) (ε ε_rem : ℝ≥0∞) (N : ℕ) (ns : List (Fin (N + 1)))
    (Hin : σ1.tapes[α]? = some ⟨N, ns⟩) :
    (∃ ε2 : List (Fin (N + 1)) → ℝ≥0∞,
      ⌜∑' n : List (Fin (N + 1)),
        (if n.length = p then 1 / ((N : ℝ≥0∞) + 1) ^ p * ε2 n else 0) ≤ ε⌝ ∗
      ∀ n, ⌜n.length = p⌝ -∗ |={∅}=>
        state_step_coupl (state_upd_tapes (·.insert α ⟨N, ns ++ n⟩) σ1) (ε_rem + ε2 n) Z)
    ⊢ state_step_coupl σ1 (ε_rem + ε) Z := by
  classical
  iintro ⟨%ε2, %Hε, H⟩
  let f : List (Fin (N + 1)) → state := fun v => state_upd_tapes (·.insert α ⟨N, ns ++ v⟩) σ1
  have hf : Function.Injective f := fun a b h =>
    (List.append_cancel_left (state_upd_tapes_same _ _ _ _ _ _ h)).symm
  let g : List (Fin (N + 1)) → ℝ≥0∞ := fun v => if v.length = p then ε2 v else 0
  iapply state_step_coupl_iterM_state_adv_comp p α σ1 Z (ε_rem + ε)
    (mem_get_active_of_lookup σ1 α _ Hin)
  iexists (fun σ' => ∃ v, v.length = p ∧ σ' = f v), 0,
    (fun σ' => ε_rem + (partial_inv_fun f σ').elim 0 g)
  isplitr
  · ipureintro
    exact ⟨⊤, fun _ => le_top⟩
  isplitr
  · ipureintro
    rw [zero_add, iterM_state_step_unfold σ1 N p α ns Hin, Expval_dmap]
    have hc : ∀ v, (partial_inv_fun f (f v)).elim 0 g = g v := fun v => by
      rw [partial_inv_fun_inj hf]; rfl
    simp only [Function.comp_def]
    rw [show (fun v => ε_rem + (partial_inv_fun f (f v)).elim 0 g) = fun v => ε_rem + g v from
      funext fun v => by rw [hc], Expval_plus, Expval_const, dunifv_mass, mul_one]
    refine add_le_add le_rfl (le_trans (le_of_eq ?_) Hε)
    unfold Expval
    congr 1
    funext v
    simp only [g, dunifv_pmf]
    split_ifs
    · push_cast
      rw [one_div]
    · simp
  isplitr
  · ipureintro
    exact pgl_iterM_state N p σ1 α ns Hin
  iintro %σ2 %⟨v, Hv, Hσ2⟩
  subst Hσ2
  have hp : (partial_inv_fun f (f v)).elim 0 g = ε2 v := by
    rw [partial_inv_fun_inj hf]
    simp [g, Hv]
  beta_reduce
  rw [hp]
  iapply H $$ %v %Hv

/-- Rocq: `state_step_coupl_state_adv_comp_con_prob_lang`. (Proved directly from
`state_step_coupl_state_adv_comp`, rather than from the `iterM` version with `p = 1`.) -/
theorem state_step_coupl_state_adv_comp_con_prob_lang (α : Loc) (σ1 : state)
    (Z : state → ℝ≥0∞ → IProp GF) (ε ε_rem : ℝ≥0∞) (N : ℕ) (ns : List (Fin (N + 1)))
    (Hin : σ1.tapes[α]? = some ⟨N, ns⟩) :
    (∃ ε2 : Fin (N + 1) → ℝ≥0∞,
      ⌜∑' n, 1 / ((N : ℝ≥0∞) + 1) * ε2 n ≤ ε⌝ ∗
      ∀ n, |={∅}=>
        state_step_coupl (state_upd_tapes (·.insert α ⟨N, ns ++ [n]⟩) σ1) (ε_rem + ε2 n) Z)
    ⊢ state_step_coupl σ1 (ε_rem + ε) Z := by
  iintro ⟨%ε2, %Hε, H⟩
  let f : Fin (N + 1) → state := fun n => state_upd_tapes (·.insert α ⟨N, ns ++ [n]⟩) σ1
  have hf : Function.Injective f := fun a b h => (state_upd_tapes_same' _ _ _ _ _ _ _ h)
  iapply state_step_coupl_state_adv_comp α σ1 Z (ε_rem + ε) (mem_get_active_of_lookup σ1 α _ Hin)
  iexists (fun σ' => ∃ n, σ' = f n), 0, (fun σ' => ε_rem + (partial_inv_fun f σ').elim 0 ε2)
  isplitr
  · ipureintro
    exact ⟨⊤, fun _ => le_top⟩
  isplitr
  · ipureintro
    rw [zero_add, state_step_unfold σ1 α N ns Hin, Expval_dmap]
    have hc : ∀ n, (partial_inv_fun f (f n)).elim 0 ε2 = ε2 n := fun n => by
      rw [partial_inv_fun_inj hf]; rfl
    simp only [Function.comp_def]
    rw [show (fun n => ε_rem + (partial_inv_fun f (f n)).elim 0 ε2) = fun n => ε_rem + ε2 n from
      funext fun n => by rw [hc], Expval_plus, Expval_const, dunifP_mass, mul_one]
    refine add_le_add le_rfl (le_trans (le_of_eq ?_) Hε)
    unfold Expval
    congr 1
    funext n
    rw [dunifP_pmf, one_div]
    push_cast
    rfl
  isplitr
  · ipureintro
    exact pgl_state N σ1 α ns Hin
  iintro %σ2 %⟨n, Hσ2⟩
  subst Hσ2
  beta_reduce
  rw [show (partial_inv_fun f (f n)).elim 0 ε2 = ε2 n by rw [partial_inv_fun_inj hf]; rfl]
  iapply H $$ %n

/-- Helper: the proof of `state_update_presample_exp`, which is stated here since
`wp_presample` and `wp_presample_adv_comp` are derived from it. -/
theorem state_update_presample_exp_aux (E : CoPset) (α : Loc) (N : ℕ) (ns : List ℕ)
    (ε1 : ℝ≥0∞) (ε2 : Fin (N + 1) → ℝ≥0∞) (Hsum : ∑' n, 1 / ((N : ℝ≥0∞) + 1) * ε2 n ≤ ε1) :
    ⊢ α ↪N (N; ns) -∗ ↯ ε1 -∗
      state_update E E iprop(∃ n : Fin (N + 1), α ↪N (N; ns ++ [(n : ℕ)]) ∗ ↯ (ε2 n)) := by
  unfold state_update state_update_def nat_tape
  simp only [conerisGS_state_interp_eq, conerisGS_err_interp_eq]
  iintro ⟨%ns', %Hmap, Hα⟩ Hε %σ1 %ε_now ⟨⟨Hh, Ht⟩, Hs⟩
  unfold tapes_auth
  icombine Ht Hα gives %Hlookup
  rw [loc_map_get?_eq] at Hlookup
  ihave %Hle := ErrorCredit.supply_bound $$ Hs Hε
  imod ErrorCredit.supply_decrease $$ Hs Hε with Hs
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply state_step_coupl_mono_err (ε_now - ε1 + ε1) ε_now _ _ (tsub_add_cancel_of_le Hle).le
  iapply state_step_coupl_state_adv_comp_con_prob_lang α σ1 _ ε1 (ε_now - ε1) N ns' Hlookup
  iexists ε2
  isplitr
  · ipureintro
    exact Hsum
  iintro %n
  by_cases hlt : ε_now - ε1 + ε2 n < 1
  · imod ErrorCredit.supply_increase hlt $$ Hs with ⟨Hs, Hε⟩
    imod ghost_map_update (⟨N, ns' ++ [n]⟩ : tape) $$ Ht Hα with ⟨Ht, Hα⟩
    rw [loc_map_insert_eq]
    imodintro
    iapply state_step_coupl_ret
    imod Hclose
    imodintro
    simp only [state_upd_tapes_heap', state_upd_tapes_tapes]
    iframe Hh Ht Hs
    iexists n
    iframe Hε
    iexists ns' ++ [n]
    iframe Hα
    ipureintro
    simp [Hmap]
  · imodintro
    iapply state_step_coupl_ret_err_ge_1 _ _ _ (not_lt.1 hlt)

/-- Rocq: `wp_presample`. -/
theorem wp_presample (N : ℕ) {e : expr} (α : Loc) (ns : List ℕ) :
    ▷ α ↪N (N; ns) ∗ (∀ n : ℕ, α ↪N (N; ns ++ [n]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }} := by
  iintro ⟨>Hα, Hwp⟩
  ihave Hε := ErrorCredit.zero (GF := GF)
  imod Hε
  imod state_update_presample_exp_aux E α N ns 0 (fun _ => 0) (by simp) $$ Hα Hε
    with ⟨%n, Hα, -⟩
  iapply Hwp $$ %(n : ℕ) Hα

/-- Rocq: `wp_presample_adv_comp`. -/
theorem wp_presample_adv_comp (N : ℕ) {e : expr} (α : Loc) (ns : List ℕ) (ε1 : ℝ≥0∞)
    (ε2 : Fin (N + 1) → ℝ≥0∞) (Hsum : ∑' n, 1 / ((N : ℝ≥0∞) + 1) * ε2 n ≤ ε1) :
    ▷ α ↪N (N; ns) ∗ ↯ ε1 ∗
      (∀ n : Fin (N + 1), ↯ (ε2 n) ∗ α ↪N (N; ns ++ [(n : ℕ)]) -∗ WP e @ E {{ Φ }})
      ⊢ WP e @ E {{ Φ }} := by
  iintro ⟨>Hα, Hε, Hwp⟩
  imod state_update_presample_exp_aux E α N ns ε1 ε2 Hsum $$ Hα Hε with ⟨%n, Hα, Hε⟩
  iapply Hwp $$ %n
  iframe

/-- Rocq: `wp_update_presample`. -/
theorem wp_update_presample (E : CoPset) (α : Loc) (N : ℕ) (ns : List ℕ) :
    ⊢ α ↪N (N; ns) -∗ wp_update E iprop(∃ n : ℕ, α ↪N (N; ns ++ [n])) := by
  unfold wp_update wp_update_def
  iintro Hα %e %Ψ Hwp
  iapply wp_presample N α ns
  isplitl [Hα]
  · inext
    iexact Hα
  · iintro %n Hα
    iapply Hwp
    iexists n
    iexact Hα

/-- Rocq: `wp_update_presample_exp`. -/
theorem wp_update_presample_exp (E : CoPset) (α : Loc) (N : ℕ) (ns : List ℕ) (ε1 : ℝ≥0∞)
    (ε2 : Fin (N + 1) → ℝ≥0∞) (Hsum : ∑' n, 1 / ((N : ℝ≥0∞) + 1) * ε2 n ≤ ε1) :
    ⊢ α ↪N (N; ns) ∗ ↯ ε1 -∗
      wp_update E iprop(∃ n : Fin (N + 1), α ↪N (N; ns ++ [(n : ℕ)]) ∗ ↯ (ε2 n)) := by
  unfold wp_update wp_update_def
  iintro ⟨Hα, Hε1⟩ %e %Ψ Hwp
  iapply wp_presample_adv_comp N α ns ε1 ε2 Hsum
  iframe Hε1
  isplitl [Hα]
  · inext
    iexact Hα
  · iintro %n ⟨Hε2, Hα⟩
    iapply Hwp
    iexists n
    iframe

/-- Rocq: `wp_update_presample_exp'`. -/
theorem wp_update_presample_exp' (E : CoPset) (α : Loc) (N : ℕ) (ns : List ℕ) (ε1 : ℝ≥0∞)
    (ε2 : ℕ → ℝ≥0∞)
    (Hsum : ∑' n, (if n ≤ N then 1 / ((N : ℝ≥0∞) + 1) * ε2 n else 0) ≤ ε1) :
    ⊢ α ↪N (N; ns) ∗ ↯ ε1 -∗ wp_update E iprop(∃ n : ℕ, α ↪N (N; ns ++ [n]) ∗ ↯ (ε2 n)) := by
  have H' : ∑' n : Fin (N + 1), 1 / ((N : ℝ≥0∞) + 1) * ε2 n ≤ ε1 := by
    rwa [SeriesC_nat_bounded_fin (fun n => 1 / ((N : ℝ≥0∞) + 1) * ε2 n) N] at Hsum
  iintro H
  ihave K := wp_update_presample_exp E α N ns ε1 (fun x => ε2 x) H' $$ H
  iapply wp_update_mono $$ [K]
  iframe K
  iintro ⟨%n, H1, H2⟩
  iexists (n : ℕ)
  iframe

/-- Rocq: `state_update_presample_iterM_exp`. Rocq's `(length n =? p)` is `n.length = p`. -/
theorem state_update_presample_iterM_exp (E : CoPset) (α : Loc) (N : ℕ) (ns : List ℕ) (p : ℕ)
    (ε1 : ℝ≥0∞) (ε2 : List (Fin (N + 1)) → ℝ≥0∞)
    (Hsum : ∑' n : List (Fin (N + 1)),
      (if n.length = p then 1 / ((N : ℝ≥0∞) + 1) ^ p * ε2 n else 0) ≤ ε1) :
    ⊢ α ↪N (N; ns) -∗ ↯ ε1 -∗
      state_update E E iprop(∃ n : List (Fin (N + 1)),
        α ↪N (N; ns ++ n.map (↑)) ∗ ↯ (ε2 n) ∗ ⌜n.length = p⌝) := by
  unfold state_update state_update_def nat_tape
  simp only [conerisGS_state_interp_eq, conerisGS_err_interp_eq]
  iintro ⟨%ns', %Hmap, Hα⟩ Hε %σ1 %ε_now ⟨⟨Hh, Ht⟩, Hs⟩
  unfold tapes_auth
  icombine Ht Hα gives %Hlookup
  rw [loc_map_get?_eq] at Hlookup
  ihave %Hle := ErrorCredit.supply_bound $$ Hs Hε
  imod ErrorCredit.supply_decrease $$ Hs Hε with Hs
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply state_step_coupl_mono_err (ε_now - ε1 + ε1) ε_now _ _ (tsub_add_cancel_of_le Hle).le
  iapply state_step_coupl_iterM_state_adv_comp_con_prob_lang p α σ1 _ ε1 (ε_now - ε1) N ns'
    Hlookup
  iexists ε2
  isplitr
  · ipureintro
    exact Hsum
  iintro %sample %Hlen
  by_cases hlt : ε_now - ε1 + ε2 sample < 1
  · imod ErrorCredit.supply_increase hlt $$ Hs with ⟨Hs, Hε⟩
    imod ghost_map_update (⟨N, ns' ++ sample⟩ : tape) $$ Ht Hα with ⟨Ht, Hα⟩
    rw [loc_map_insert_eq]
    imodintro
    iapply state_step_coupl_ret
    imod Hclose
    imodintro
    simp only [state_upd_tapes_heap', state_upd_tapes_tapes]
    iframe Hh Ht Hs
    iexists sample
    iframe Hε
    isplitl
    · iexists ns' ++ sample
      iframe Hα
      ipureintro
      simp [Hmap]
    · ipureintro
      exact Hlen
  · imodintro
    iapply state_step_coupl_ret_err_ge_1 _ _ _ (not_lt.1 hlt)

/-- Rocq: `state_update_presample_exp`. -/
theorem state_update_presample_exp (E : CoPset) (α : Loc) (N : ℕ) (ns : List ℕ) (ε1 : ℝ≥0∞)
    (ε2 : Fin (N + 1) → ℝ≥0∞) (Hsum : ∑' n, 1 / ((N : ℝ≥0∞) + 1) * ε2 n ≤ ε1) :
    ⊢ α ↪N (N; ns) -∗ ↯ ε1 -∗
      state_update E E iprop(∃ n : Fin (N + 1), α ↪N (N; ns ++ [(n : ℕ)]) ∗ ↯ (ε2 n)) :=
  state_update_presample_exp_aux E α N ns ε1 ε2 Hsum

/-- Rocq: `state_step_err_set_in_out` (Rocq's `gset nat` is a `Finset ℕ`). -/
theorem state_step_err_set_in_out (N : ℕ) (bad : Finset ℕ) (ε εI εO : ℝ≥0∞) (E : CoPset)
    (α : Loc) (ns : List ℕ) (Hlen : ∀ n ∈ bad, n < N + 1)
    (Hleq : εI * bad.card + εO * ((N : ℝ≥0∞) + 1 - bad.card) ≤ ε * ((N : ℝ≥0∞) + 1)) :
    ⊢ α ↪N (N; ns) -∗ ↯ ε -∗
      state_update E E iprop(∃ x : Fin (N + 1),
        ((⌜(x : ℕ) ∉ bad⌝ ∗ ↯ εO) ∨ (⌜(x : ℕ) ∈ bad⌝ ∗ ↯ εI)) ∗
          α ↪N (N; ns ++ [(x : ℕ)])) := by
  iintro Htape Herr
  imod state_update_presample_exp E α N ns ε (fun x => if (x : ℕ) ∈ bad then εI else εO)
    (SeriesC_in_out_le N bad ε εI εO Hlen Hleq) $$ Htape Herr with ⟨%x, Htape, Herr⟩
  imodintro
  iexists x
  iframe Htape
  by_cases h : (x : ℕ) ∈ bad
  · simp only [ite_eq_left h]
    iright
    iframe Herr
    ipureintro
    exact h
  · simp only [ite_eq_right h]
    ileft
    iframe Herr
    ipureintro
    exact h

/-- Rocq: `wp_couple_empty_tape_adv_comp`. -/
theorem wp_couple_empty_tape_adv_comp (α : Loc) (N : ℕ) (ε1 : ℝ≥0∞) (ε2 : ℕ → ℝ≥0∞)
    (Hsum : ∑' n, (if n ≤ N then 1 / ((N : ℝ≥0∞) + 1) * ε2 n else 0) ≤ ε1) :
    {{ α ↪N (N; []) ∗ ↯ ε1 }} (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV (LitLbl α)))) @ E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); α ↪N (N; []) ∗ ↯ (ε2 n) }} := by
  iintro %Ψ ⟨Hα, Herr⟩ HΨ
  imod wp_update_presample_exp' E α N [] ε1 ε2 Hsum $$ [Hα Herr] with ⟨%n, Hα, Hε⟩
  · iframe
  simp only [List.nil_append]
  iapply wp_rand_tape N α n [] (N : ℤ) (by simp) $$ %Ψ [Hα]
  · inext
    iexact Hα
  iintro !> ⟨Hα, -⟩
  iapply HΨ
  iframe

end rules

end Coneris
