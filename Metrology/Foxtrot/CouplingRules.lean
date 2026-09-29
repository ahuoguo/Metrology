module

public import Metrology.Foxtrot.ProofMode

/-!
# Coupling rules of Foxtrot (part 1)

Ported from clutch/theories/foxtrot/coupling_rules.v (lines 1–1618; the von Neumann lemmas
and the associativity / toss / tape / label rules of the rest of the file are ported in
separate files importing this one).

## Rocq → Lean map
* `ARcoupl_steps_ctx_bind_r μ e1' σ1' R ε K Hv Hcpl` (same name; `Hv` is the `to_val = None`
  hypothesis, Rocq introduces the two hypotheses with swapped names).
* `wp_couple_rand_rand N f Hbij j z K hN Hdom`, `wp_couple_rand_rand' N f Hbij j z K hN Hdom`:
  the Rocq instance `` `{Bij nat nat f} `` is the hypothesis `Hbij : Function.Bijective f`,
  `TCEq N (Z.to_nat z)` is `hN : N = z.toNat`, `(n < S N)%nat` is `n < N + 1`.
  Rocq's `f_inv f` is `(Equiv.ofBijective f Hbij).symm`.
* `wp_couple_rand_two_rands N M f K K' z z' x j j' _hN _hM hx Hcond1 Hcond2 Hcond3`
  (the `TCEq` hypotheses are kept, although, as in Rocq, the RHS programs are `rand #N` and
  `rand #M` for `N M : ℕ`; `x = Z.of_nat (S N * S M - 1)` is `hx`).
* `wp_couple_fragmented_rand_rand_inj f Hinj j K Hineq Hdom` (`{M N}` implicit, as in Rocq;
  `Inj (=) (=) f` is `Hinj : Function.Injective f`).
* `pupd_couple_fragmented_tape_rand_inj_rev' f Hinj ns α j K E ε Hineq Hdom`.
* Texan triples are iris-lean's `{{ P }} (e) @ s; E {{ (n : ℕ), RET v; Q }}` (with implicit
  `{s E}`); `rand #z` is `Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))`, `#n` for
  `n : ℕ` is `Val (LitV (LitInt (n : ℤ)))`.

## Design choices / deviations
* Errors are `ℝ≥0∞`: the hypothesis `0 <= ε` of `pupd_couple_fragmented_tape_rand_inj_rev'`
  vanishes; the error `S M / (S M - S N) * ε` is
  `((M+1 : ℕ) : ℝ≥0∞) / (((M+1 : ℕ) : ℝ≥0∞) - ((N+1 : ℕ) : ℝ≥0∞)) * ε`. Rocq's
  `nnreal_minus ε_now ε'` is `εnow - ε` (truncated subtraction, with `ε ≤ εnow` from
  `ErrorCredit.supply_bound`), and `ε_now + ε' * S N / (S M - S N)` is `εnow + δ` with
  `δ = ε * (N + 1) / (M - N)` (`(M - N : ℕ)` cast). Rocq's `ec_supply_decrease` /
  `ec_supply_increase` / `ec_eq` are `ErrorCredit.supply_decrease` / `supply_increase` /
  `ErrorCredit.ext`.
* The Rocq proofs work with `fin (S N)`-valued samples (`restr_bij_fin`, `restr_inj_fin`,
  `nat_to_fin`); here `dunifP N : Distr (Fin (N + 1))` is used directly, with the restricted
  function `fun a => ⟨f a, Hdom a a.2⟩`, and bijectivity from `Finite.injective_iff_bijective`.
* The couplings are proved by rewriting both sides into `dbind`/`dmap` of uniform
  distributions (helpers `prim_step_rand`, `step'_fill_rand`, `two_step_osch_lim_exec`,
  `frag_osch_lim_exec`) and `ARcoupl_dbind'`, `ARcoupl_map`, `ARcoupl_eq`, `ARcoupl_dunif`,
  `ARcoupl_dret`, `dunifP_decompose`, `dunif_fragmented` (Rocq: the same lemmas plus
  `instantiate`d relations). The coupling relations are stated up front.
* The injectivity side conditions are proved by reading the thread `j` back from the recorded
  configurations of the full-information history (`fill_lit_nat_inj`), instead of
  `list_lookup_insert_eq` + `simplify_eq` on the final configurations.
* The expected-error calculation of `pupd_couple_fragmented_tape_rand_inj_rev'` (Rocq: gsets
  of `fin`s, `SeriesC_fin_in_set`, `size_difference`, real arithmetic) is the helper
  `frag_expval_calc`, done with `Finset.sum_ite` and cardinalities; the final `ec_eq`
  computation is `frag_err_eq`.
* Rocq destructs the RHS configuration `ρ1` as `[l s]`; here too (`%⟨l, s'⟩`), and the
  `CPState`-typed pairs are handled via `spec_coupl_ret_pair` / explicit `spec_coupl_rec`
  arguments, since `(l, s')` and `CPState` do not unify at reducible transparency.
* Rocq's `ghost_map_elem_ne` on the two spec threads of `wp_couple_rand_two_rands` is the
  helper `spec_prog_frag_ne`.

## Omitted
* All commented-out Rocq lemmas in lines 1–1618 (`wp_couple_tapes`, `wp_couple_tapes_bij`,
  `wp_couple_tapes_rev`, `wp_rand_avoid_l/r`, `wp_couple_rand_rand_inj`,
  `wp_couple_rand_rand_leq`, `wp_couple_rand_rand_rev_inj`, `wp_couple_rand_rand_rev_leq`,
  `wp_couple_rand_rand_avoid(')`, `length_remove_dups`, `wp_couple_fragmented_rand_rand_leq`,
  `wp_couple_fragmented_rand_rand_inj_rev`, `wp_couple_fragmented_rand_rand_leq_rev'`,
  `wp_couple_exp*`).
* `Local Opaque`/`Local Transparent` directives (no Lean counterpart needed).
* The later ranges of `coupling_rules.v` contain no `Local` helper lemmas reused across chunks.

## Added helpers (not in Rocq)
`fill_injective`, `fill_lit_nat_inj`, `bij_restr_inv` (Rocq: `restr_bij_fin` +
`f_inv_restr`), `prim_step_fill_rand`, `prim_step_rand`, `prim_step_rand_nat`, `reducible_rand`,
`step'_fill_rand`, `step'_fill_rand_nat`, `two_step_osch` (+ `two_step_osch_lim_exec`),
`frag_osch` (+ `frag_osch_lim_exec`), `frag_expval_calc`, `frag_err_eq`, `spec_prog_frag_ne`.
These are generic and may be reused by the other coupling-rule files (e.g. `step'_fill_rand`,
`fill_lit_nat_inj`, `spec_prog_frag_ne`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

/-! ## Local helpers (not in Rocq) -/

section helpers

/-- Helper (Rocq: the `Inj` instance `fill_inj`): `fill K` is injective. -/
theorem fill_injective (K : List ectx_item) : Function.Injective (fill K) := by
  induction K with
  | nil => exact fun _ _ h => h
  | cons Ki K ih => exact fun x y h => fill_item_inj Ki (ih h)

/-- Helper: `fill K #n` determines `n`. -/
theorem fill_lit_nat_inj (K : List ectx_item) {n m : ℕ}
    (h : fill K (Val (LitV (LitInt (n : ℤ)))) = fill K (Val (LitV (LitInt (m : ℤ))))) : n = m := by
  have := fill_injective K h
  injection this with this
  injection this with this
  injection this with this
  exact Int.ofNat.inj this

/-- Helper (Rocq: `restr_bij_fin` + `f_inv_restr`): a bijection `f` of `ℕ` mapping `[0, N]`
into itself maps it onto itself, hence so does its inverse. -/
theorem bij_restr_inv (N : ℕ) (f : ℕ → ℕ) (Hbij : Function.Bijective f)
    (Hdom : ∀ n : ℕ, n < N + 1 → f n < N + 1) (n : ℕ) (hn : n < N + 1) :
    (Equiv.ofBijective f Hbij).symm n < N + 1 := by
  let ff : Fin (N + 1) → Fin (N + 1) := fun a => ⟨f a, Hdom a a.2⟩
  have Hff_inj : Function.Injective ff := fun a b h => Fin.ext (Hbij.1 (congrArg Fin.val h))
  obtain ⟨a, ha⟩ := (Finite.injective_iff_bijective.1 Hff_inj).2 ⟨n, hn⟩
  have : f a = n := congrArg Fin.val ha
  rw [← this, Equiv.ofBijective_symm_apply_apply]
  exact a.2

/-- Helper: the `prim_step` of `rand #z` in an evaluation context. -/
theorem prim_step_fill_rand (K : List ectx_item) (z : ℤ) (σ : state) :
    prim_step (Λ := con_prob_lang) (fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit)))) σ =
      dmap (fun n : Fin (z.toNat + 1) =>
        ((fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))), σ, []) : expr × state × List expr))
        (dunifP z.toNat) :=
  prim_step_fill_head K _ σ (dunifP z.toNat)
    (fun n : Fin (z.toNat + 1) =>
      ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) : expr × state × List expr)) rfl (dunifP_mass _)

/-- Helper: the `prim_step` of `rand #z`. -/
theorem prim_step_rand (z : ℤ) (σ : state) :
    prim_step (Λ := con_prob_lang) (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ =
      dmap (fun n : Fin (z.toNat + 1) =>
        ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) : expr × state × List expr))
        (dunifP z.toNat) :=
  prim_step_fill_rand [] z σ

/-- Helper: `rand #z` is reducible. -/
theorem reducible_rand (z : ℤ) (σ : state) :
    reducible (Λ := con_prob_lang) (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ := by
  refine ⟨((Val (LitV (LitInt ((0 : ℕ) : ℤ))), σ, []) : expr × state × List expr), ?_⟩
  rw [prim_step_rand, dmap_pos]
  exact ⟨0, rfl, dunifP_pos _ _⟩

/-- Helper: one step of the RHS thread `j` running `fill K (rand #z)`. -/
theorem step'_fill_rand (j : ℕ) (ρ : CPState) (K : List ectx_item) (z : ℤ)
    (Hsome : ρ.1[j]? = some (fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))))) :
    step' j ρ =
      dmap (fun n : Fin (z.toNat + 1) =>
        ((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), ρ.2) : CPState))
        (dunifP z.toNat) := by
  have Hval : ConProbLang.to_val (Λ := con_prob_lang)
      (fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit)))) = none :=
    conEctxiLanguage.fill_not_val (Λ := con_prob_ectxi_lang) K _ rfl
  simp only [step', Hsome, Hval]
  rw [prim_step_fill_rand]
  refine (dmap_comp (β := expr × state × List expr) (δ := CPState) _ _ _).trans ?_
  congr 1
  funext n
  simp [Function.comp]

/-- Helper: `step'_fill_rand` for a natural-number bound `rand #N`. -/
theorem step'_fill_rand_nat (j : ℕ) (ρ : CPState) (K : List ectx_item) (N : ℕ)
    (Hsome : ρ.1[j]? = some (fill K (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV LitUnit))))) :
    step' j ρ =
      dmap (fun n : Fin (N + 1) =>
        ((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), ρ.2) : CPState))
        (dunifP N) :=
  step'_fill_rand j ρ K (N : ℤ) Hsome

/-- Helper: `prim_step_rand` for a natural-number bound `rand #N`. -/
theorem prim_step_rand_nat (N : ℕ) (σ : state) :
    prim_step (Λ := con_prob_lang) (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV LitUnit))) σ =
      dmap (fun n : Fin (N + 1) =>
        ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) : expr × state × List expr))
        (dunifP N) :=
  prim_step_rand (N : ℤ) σ

/-- Helper: the full-information scheduler of `wp_couple_rand_two_rands` (Rocq: inline), which
steps thread `j`, then thread `j'`, then stops. -/
def two_step_osch (j j' : ℕ) : full_info_oscheduler :=
  full_info_cons_osch (fun _ => dret j) (fun _ => full_info_one_step_stutter_osch j')

/-- Helper: the limit execution of `two_step_osch` on two `rand`s (Rocq: inline in
`wp_couple_rand_two_rands`). -/
theorem two_step_osch_lim_exec (j j' : ℕ) (K K' : List ectx_item) (N M : ℕ) (ρ : CPState)
    (hne : j ≠ j')
    (Hsome : ρ.1[j]? = some (fill K (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV LitUnit)))))
    (Hsome' : ρ.1[j']? = some (fill K' (Rand (Val (LitV (LitInt (M : ℤ)))) (Val (LitV LitUnit))))) :
    osch_lim_exec (two_step_osch j j').fi_osch ([], ρ) =
      dunifP N ≫= fun n : Fin (N + 1) => dmap (fun m : Fin (M + 1) =>
        (([(cfg_to_cfg' ρ, j),
          (cfg_to_cfg' ((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), ρ.2) : CPState),
            j'),
          (cfg_to_cfg' (((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))).set j'
            (fill K' (Val (LitV (LitInt ((m : ℕ) : ℤ))))), ρ.2) : CPState),
            ((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))).set j'
            (fill K' (Val (LitV (LitInt ((m : ℕ) : ℤ)))))).length)] : full_info_state),
          (((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))).set j'
            (fill K' (Val (LitV (LitInt ((m : ℕ) : ℤ))))), ρ.2) : CPState))) (dunifP M) := by
  unfold two_step_osch
  rw [full_info_cons_osch_lim_exec, dret_id_left, step'_fill_rand_nat j ρ K N Hsome, dmap]
  refine (dbind_assoc (β := CPState) _ _ _).symm.trans ?_
  refine dbind_ext_right _ _ _ fun n => ?_
  refine (dret_id_left (α := CPState) _ _).trans ?_
  have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, j)] (full_info_one_step_stutter_osch j') []
    ((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), ρ.2) : CPState)
  simp only [List.append_nil] at this
  have Hsome'' : ((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), ρ.2) : CPState).1[j']? =
      some (fill K' (Rand (Val (LitV (LitInt (M : ℤ)))) (Val (LitV LitUnit)))) := by
    simpa [List.getElem?_set_ne hne] using Hsome'
  refine this.trans ?_
  refine (congrArg (dmap _) ((full_info_one_step_stutter_osch_lim_exec j' _).trans
    ((congrArg (dmap _) (step'_fill_rand_nat j' _ K' M Hsome'')).trans
      (dmap_comp _ _ _)))).trans ?_
  exact dmap_comp _ _ _

open Classical in
/-- Helper: the full-information scheduler of `wp_couple_fragmented_rand_rand_inj` (Rocq: inline).
It samples `n ≤ N`; if `n = f m` for some `m ≤ M` it steps thread `j` (and then stutters once),
otherwise it records `n` by stuttering on the out-of-bounds thread `len + n`. -/
def frag_osch (M N : ℕ) (f : ℕ → ℕ) (j len : ℕ) : full_info_oscheduler :=
  full_info_cons_osch
    (fun _ => dmap (fun n : Fin (N + 1) =>
      if ∃ m : ℕ, m ≤ M ∧ f m = (n : ℕ) then j else len + (n : ℕ)) (dunifP N))
    (fun x => if x = j then full_info_stutter_osch full_info_inhabitant else full_info_inhabitant)

open Classical in
/-- Helper: the limit execution of `frag_osch`. -/
theorem frag_osch_lim_exec (M N : ℕ) (f : ℕ → ℕ) (j : ℕ) (K : List ectx_item) (ρ : CPState)
    (Hsome : ρ.1[j]? = some (fill K (Rand (Val (LitV (LitInt (M : ℤ)))) (Val (LitV LitUnit))))) :
    osch_lim_exec (frag_osch M N f j ρ.1.length).fi_osch ([], ρ) =
      dunifP N ≫= fun n : Fin (N + 1) =>
        if ∃ m : ℕ, m ≤ M ∧ f m = (n : ℕ) then
          dmap (fun m' : Fin (M + 1) =>
            (([(cfg_to_cfg' ρ, j),
              (cfg_to_cfg' ((ρ.1.set j (fill K (Val (LitV (LitInt ((m' : ℕ) : ℤ))))), ρ.2) :
                CPState), ρ.1.length)] : full_info_state),
              ((ρ.1.set j (fill K (Val (LitV (LitInt ((m' : ℕ) : ℤ))))), ρ.2) : CPState)))
            (dunifP M)
        else dret (([(cfg_to_cfg' ρ, ρ.1.length + (n : ℕ))] : full_info_state), ρ) := by
  have Hj : j < ρ.1.length := (List.getElem?_eq_some_iff.1 Hsome).1
  unfold frag_osch
  rw [full_info_cons_osch_lim_exec, dmap]
  refine (dbind_assoc (β := ℕ) _ _ _).symm.trans ?_
  refine dbind_ext_right _ _ _ fun n => ?_
  refine (dret_id_left (α := ℕ) _ _).trans ?_
  by_cases h : ∃ m : ℕ, m ≤ M ∧ f m = (n : ℕ)
  · simp only [h, ↓reduceIte]
    rw [step'_fill_rand_nat j ρ K M Hsome, dmap]
    refine (dbind_assoc (β := CPState) _ _ _).symm.trans ?_
    refine dbind_ext_right _ _ _ fun m' => ?_
    refine (dret_id_left (α := CPState) _ _).trans ?_
    have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, j)]
      (full_info_stutter_osch full_info_inhabitant) []
      ((ρ.1.set j (fill K (Val (LitV (LitInt ((m' : ℕ) : ℤ))))), ρ.2) : CPState)
    simp only [List.append_nil] at this
    refine this.trans ?_
    refine (congrArg (dmap _) ((full_info_stutter_osch_lim_exec _ _).trans
      (congrArg (dmap _) (full_info_inhabitant_lim_exec _)))).trans ?_
    simp only [dmap_dret]
    simp [List.length_set]
  · simp only [h, ↓reduceIte]
    rw [out_of_bounds_step' _ _ (Nat.le_add_right _ _)]
    refine (dret_id_left (α := CPState) _ _).trans ?_
    have hne : ¬ (ρ.1.length + (n : ℕ) = j) := by omega
    simp only [hne, ↓reduceIte]
    have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, ρ.1.length + (n : ℕ))]
      full_info_inhabitant [] ρ
    simp only [List.append_nil] at this
    refine this.trans ?_
    rw [full_info_inhabitant_lim_exec, dmap_dret]
    rfl

open Classical in
/-- Helper (Rocq: the "hardcore calculation" inline in
`pupd_couple_fragmented_tape_rand_inj_rev'`): the expected error after sampling `m ≤ M`
uniformly, paying `ε` when `m` is in the image of `f` on `[0, N]` and receiving
`ε * (N + 1) / (M - N)` otherwise, is unchanged. -/
theorem frag_expval_calc (M N : ℕ) (f : ℕ → ℕ) (Hinj : Function.Injective f)
    (Hdom : ∀ n : ℕ, n < N + 1 → f n < M + 1) (Hineq : N < M) (εnow ε : ℝ≥0∞) (Hle : ε ≤ εnow) :
    ∑' m : Fin (M + 1), dunifP M m *
      (if ∃ n : Fin (N + 1), f n = (m : ℕ) then εnow - ε
        else εnow + ε * ((N + 1 : ℕ) : ℝ≥0∞) / ((M - N : ℕ) : ℝ≥0∞)) = εnow := by
  let F : Fin (N + 1) → Fin (M + 1) := fun n => ⟨f n, Hdom n n.2⟩
  have HF : Function.Injective F := fun a b h => Fin.ext (Hinj (congrArg Fin.val h))
  have Hfilt : (Finset.univ.filter fun m : Fin (M + 1) => ∃ n : Fin (N + 1), f n = (m : ℕ)) =
      Finset.univ.image F := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, Fin.ext hn⟩, fun ⟨n, hn⟩ => ⟨n, congrArg Fin.val hn⟩⟩
  have Hcard1 : (Finset.univ.filter fun m : Fin (M + 1) =>
      ∃ n : Fin (N + 1), f n = (m : ℕ)).card = N + 1 := by
    rw [Hfilt, Finset.card_image_of_injective _ HF, Finset.card_univ, Fintype.card_fin]
  have Hcard2 : (Finset.univ.filter fun m : Fin (M + 1) =>
      ¬ ∃ n : Fin (N + 1), f n = (m : ℕ)).card = M - N := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (M + 1)))) (fun m : Fin (M + 1) =>
        ∃ n : Fin (N + 1), f n = (m : ℕ))
    rw [Hcard1, Finset.card_univ, Fintype.card_fin] at this
    omega
  have HMN : ((M - N : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : M - N ≠ 0)
  have HMN' : ((M - N : ℕ) : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.natCast_ne_top _
  simp only [dunifP_pmf]
  rw [tsum_fintype, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    Hcard1, Hcard2, nsmul_eq_mul, nsmul_eq_mul, mul_add ((M - N : ℕ) : ℝ≥0∞),
    mul_div_assoc]
  have h1 : ((M - N : ℕ) : ℝ≥0∞) * (ε * (((N + 1 : ℕ) : ℝ≥0∞) / ((M - N : ℕ) : ℝ≥0∞))) =
      ((N + 1 : ℕ) : ℝ≥0∞) * ε := by
    rw [mul_left_comm, ENNReal.mul_div_cancel HMN HMN', mul_comm]
  have h2 : ((N + 1 : ℕ) : ℝ≥0∞) * (εnow - ε) +
      (((M - N : ℕ) : ℝ≥0∞) * εnow + ((N + 1 : ℕ) : ℝ≥0∞) * ε) =
      ((M + 1 : ℕ) : ℝ≥0∞) * εnow := by
    rw [add_comm (((M - N : ℕ) : ℝ≥0∞) * εnow), ← add_assoc, ← mul_add,
      tsub_add_cancel_of_le Hle, ← add_mul, ← Nat.cast_add]
    congr 2
    omega
  rw [h1, h2, ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

/-- Helper (Rocq: the final `ec_eq` computation of `pupd_couple_fragmented_tape_rand_inj_rev'`). -/
theorem frag_err_eq (M N : ℕ) (Hineq : N < M) (ε : ℝ≥0∞) :
    ε + ε * ((N + 1 : ℕ) : ℝ≥0∞) / ((M - N : ℕ) : ℝ≥0∞) =
      ((M + 1 : ℕ) : ℝ≥0∞) / (((M + 1 : ℕ) : ℝ≥0∞) - ((N + 1 : ℕ) : ℝ≥0∞)) * ε := by
  have HMN : ((M - N : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : M - N ≠ 0)
  have HMN' : ((M - N : ℕ) : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := ENNReal.natCast_ne_top _
  rw [show ((M + 1 : ℕ) : ℝ≥0∞) - ((N + 1 : ℕ) : ℝ≥0∞) = ((M - N : ℕ) : ℝ≥0∞) by
    rw [← ENNReal.natCast_sub]; congr 1; omega]
  rw [mul_div_assoc, mul_comm _ ε]
  nth_rewrite 1 [← mul_one ε]
  rw [← mul_add]
  congr 1
  rw [← ENNReal.div_self HMN HMN', ENNReal.div_add_div_same, ← Nat.cast_add]
  congr 2
  omega

end helpers

section rules

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `ARcoupl_steps_ctx_bind_r`. Helper lemma. -/
theorem ARcoupl_steps_ctx_bind_r {A : Type} [Countable A] (μ : Distr A) (e1' : expr)
    (σ1' : state) (R : A → expr × state × List expr → Prop) (ε : ℝ≥0∞) (K : List ectx_item)
    (Hv : ConProbLang.to_val (Λ := con_prob_lang) e1' = none)
    (Hcpl : ARcoupl μ (prim_step (Λ := con_prob_lang) e1' σ1') R ε) :
    ARcoupl μ (prim_step (Λ := con_prob_lang) (fill K e1') σ1')
      (fun a p => ∃ e2'', p.1 = fill K e2'' ∧ R a (e2'', p.2.1, p.2.2)) ε := by
  rw [@ConLanguageCtx.fill_dmap con_prob_lang (fill K) _ e1' σ1' Hv, dmap, ← dret_id_right μ]
  refine ARcoupl_dbind' ε 0 ε _ _ _ _ R _ (add_zero _).symm (fun a b hab => ?_) Hcpl
  exact ARcoupl_dret _ _ _ _ ⟨b.1, rfl, hab⟩

/-- Rocq: `wp_couple_rand_rand`. `rand(N) ~ rand(N)` coupling along a bijection `f`. -/
theorem wp_couple_rand_rand (N : ℕ) (f : ℕ → ℕ) (Hbij : Function.Bijective f) (j : ℕ) (z : ℤ)
    (K : List ectx_item) {s : Stuckness} {E : CoPset} (hN : N = z.toNat)
    (Hdom : ∀ n : ℕ, n < N + 1 → f n < N + 1) :
    {{ j ⤇ fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) }}
      (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ));
      (iprop(⌜n ≤ N⌝ ∗ j ⤇ fill K (Val (LitV (LitInt ((f n : ℕ) : ℤ))))) : IProp GF) }} := by
  subst hN
  -- Rocq: `restr_bij_fin`
  let ff : Fin (z.toNat + 1) → Fin (z.toNat + 1) := fun a => ⟨f a, Hdom a a.2⟩
  have Hff_inj : Function.Injective ff := fun a b h => Fin.ext (Hbij.1 (congrArg Fin.val h))
  have Hff : Function.Bijective ff := Finite.injective_iff_bijective.1 Hff_inj
  iintro %Ψ Hr HΨ
  iapply wp_lift_step_prog_couple rfl
  simp only [foxtrotGS_spec_interp_eq]
  iintro %σ1 %⟨l, s'⟩ %ε ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree l s' j _ $$ Hs Hr
  have Hj : j < l.length := (List.getElem?_eq_some_iff.1 Hsome).1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  let g1 : Fin (z.toNat + 1) → expr × state × List expr := fun n =>
    (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, [])
  let g2 : Fin (z.toNat + 1) → full_info_state × CPState := fun n =>
    ([(cfg_to_cfg' ((l, s') : CPState), j),
      (cfg_to_cfg' ((l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), s') : CPState),
        (l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))).length)],
      ((l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), s') : CPState))
  have Hlim : osch_lim_exec (full_info_one_step_stutter_osch j).fi_osch ([], ((l, s') : CPState)) =
      dmap g2 (dunifP z.toNat) := by
    exact (full_info_one_step_stutter_osch_lim_exec j _).trans
      ((congrArg (dmap _) (step'_fill_rand j ((l, s') : CPState) K z Hsome)).trans
        (dmap_comp _ _ _))
  iexists (fun x y => ∃ a, x = g1 a ∧ y = g2 (ff a)), full_info_one_step_stutter_osch j, 0,
    (fun _ => ε), ε
  isplitr
  · ipureintro
    exact reducible_rand z σ1
  isplitr
  · ipureintro
    exact fun _ => le_rfl
  isplitr
  · ipureintro
    rw [zero_add, Expval_const]
    exact mul_le_of_le_one_right zero_le (pmf_SeriesC _)
  isplitr
  · ipureintro
    rw [prim_step_rand, Hlim]
    apply ARcoupl_map
    exact ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      (fun a b h => ⟨a, rfl, by rw [h]⟩) le_rfl (ARcoupl_dunif _ ff Hff)
  isplitr
  · ipureintro
    rintro x1 x2 L y1 y2 ⟨a, rfl, h1⟩ ⟨b, rfl, h2⟩
    have hL1 : L = (g2 (ff a)).1 := congrArg Prod.fst h1
    have hL2 : L = (g2 (ff b)).1 := congrArg Prod.fst h2
    have h := congrArg (fun L : full_info_state => (L[1]?).map (fun q => q.1.1[j]?))
      (hL1.symm.trans hL2)
    simp only [g2, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
      List.getElem?_set_self Hj, Option.some.injEq] at h
    have hab : a = b := by
      exact Hff_inj (Fin.ext (fill_lit_nat_inj K h))
    subst hab
    exact ⟨rfl, (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm⟩
  iintro %e2 %σ2 %efs %l' %ρ2 %⟨a, h1, h2⟩
  simp only [g1, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
  beta_reduce
  imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((ff a : ℕ) : ℤ))))) $$ Hs Hr
    with ⟨Hs, Hr⟩
  imodintro
  inext
  imod Hclose
  imodintro
  iframe Hσ Hs Hε
  isplitl
  · iapply wp_value'
    iapply HΨ $$ %(a : ℕ)
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 a.2
    · iexact Hr
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_couple_rand_rand'`. -/
theorem wp_couple_rand_rand' (N : ℕ) (f : ℕ → ℕ) (Hbij : Function.Bijective f) (j : ℕ) (z : ℤ)
    (K : List ectx_item) {s : Stuckness} {E : CoPset} (hN : N = z.toNat)
    (Hdom : ∀ n : ℕ, n < N + 1 → f n < N + 1) :
    {{ j ⤇ fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) }}
      (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt ((f n : ℕ) : ℤ));
      (iprop(⌜n ≤ N⌝ ∗ j ⤇ fill K (Val (LitV (LitInt (n : ℤ))))) : IProp GF) }} := by
  -- Rocq: `f_inv f`, `f_inv_bij`, `f_inv_restr`
  let g : ℕ → ℕ := (Equiv.ofBijective f Hbij).symm
  have Hg : Function.Bijective g := (Equiv.ofBijective f Hbij).symm.bijective
  have Hdom' : ∀ n : ℕ, n < N + 1 → g n < N + 1 := bij_restr_inv N f Hbij Hdom
  iintro %Ψ Hr HΨ
  iapply wp_couple_rand_rand N g Hg j z K hN Hdom' $$ Hr
  inext
  iintro %n ⟨%Hn, Hj⟩
  have hfg : f (g n) = n := Equiv.ofBijective_apply_symm_apply f Hbij n
  rw [show LitV (LitInt (n : ℤ)) = LitV (LitInt ((f (g n) : ℕ) : ℤ)) by rw [hfg]]
  iapply HΨ $$ %(g n)
  isplitr
  · ipureintro
    exact Nat.lt_succ_iff.1 (Hdom' n (Nat.lt_succ_iff.2 Hn))
  · iexact Hj

attribute [local instance] specG_con_prob_lang.specG_con_prob_lang_prog in
/-- Helper (Rocq: `ghost_map_elem_ne` on the spec thread pool): two spec threads are distinct. -/
theorem spec_prog_frag_ne (j j' : ℕ) (e e' : expr) :
    j ⤇ e ⊢@{IProp GF} j' ⤇ e' -∗ ⌜j ≠ j'⌝ := by
  unfold spec_prog_frag
  iintro H1 H2
  iapply ghost_map_elem_ne _ j j' _ e e' $$ H1 H2

/-- Rocq: `wp_couple_rand_two_rands`. Coupling a `rand` on the LHS with two `rand`s on the
RHS, along a bijection `f : [0, N] × [0, M] → [0, (N+1)(M+1) - 1]`. -/
theorem wp_couple_rand_two_rands (N M : ℕ) (f : ℕ → ℕ → ℕ) (K K' : List ectx_item)
    {s : Stuckness} {E : CoPset} (z z' x : ℤ) (j j' : ℕ) (_hN : N = z.toNat) (_hM : M = z'.toNat)
    (hx : x = (((N + 1) * (M + 1) - 1 : ℕ) : ℤ))
    (Hcond1 : ∀ n m, n < N + 1 → m < M + 1 → f n m < (N + 1) * (M + 1))
    (Hcond2 : ∀ n n' m m', n < N + 1 → n' < N + 1 → m < M + 1 → m' < M + 1 →
      f n m = f n' m' → n = n' ∧ m = m')
    (Hcond3 : ∀ x, x < (N + 1) * (M + 1) → ∃ n m, n < N + 1 ∧ m < M + 1 ∧ f n m = x) :
    {{ j ⤇ fill K (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV LitUnit))) ∗
        j' ⤇ fill K' (Rand (Val (LitV (LitInt (M : ℤ)))) (Val (LitV LitUnit))) }}
      (Rand (Val (LitV (LitInt x))) (Val (LitV LitUnit))) @ s; E
    {{ (x : ℕ), RET LitV (LitInt (x : ℤ));
      (iprop(∃ n m : ℕ, ⌜n ≤ N⌝ ∗ ⌜m ≤ M⌝ ∗ ⌜x = f n m⌝ ∗
        j ⤇ fill K (Val (LitV (LitInt (n : ℤ)))) ∗
        j' ⤇ fill K' (Val (LitV (LitInt (m : ℤ))))) : IProp GF) }} := by
  subst hx
  -- Rocq: the function `f'` specialised to `fin`
  have hX : (N + 1) * (M + 1) - 1 + 1 = (N + 1) * (M + 1) := by
    have : 0 < (N + 1) * (M + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  let F : Fin (N + 1) × Fin (M + 1) → Fin ((N + 1) * (M + 1) - 1 + 1) := fun p =>
    ⟨f p.1 p.2, hX ▸ Hcond1 _ _ p.1.2 p.2.2⟩
  have HF : Function.Bijective F := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      obtain ⟨h1, h2⟩ := Hcond2 _ _ _ _ a.2 a'.2 b.2 b'.2 (congrArg Fin.val h)
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · rintro ⟨y, hy⟩
      obtain ⟨n, m, hn, hm, rfl⟩ := Hcond3 y (hX ▸ hy)
      exact ⟨(⟨n, hn⟩, ⟨m, hm⟩), rfl⟩
  have Hdecomp := dunifP_decompose N M _ F HF rfl
  iintro %Φ ⟨Hj, Hj'⟩ HΦ
  iapply wp_lift_step_prog_couple rfl
  simp only [foxtrotGS_spec_interp_eq]
  iintro %σ1 %⟨l, s'⟩ %ε ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree l s' j _ $$ Hs Hj
  ihave %Hsome' := spec_auth_prog_agree l s' j' _ $$ Hs Hj'
  ihave %Hne := spec_prog_frag_ne j j' _ _ $$ Hj Hj'
  have Hjl : j < l.length := (List.getElem?_eq_some_iff.1 Hsome).1
  have Hjl' : j' < l.length := (List.getElem?_eq_some_iff.1 Hsome').1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  let l1 : Fin (N + 1) → List expr := fun n => l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))
  let l2 : Fin (N + 1) → Fin (M + 1) → List expr := fun n m =>
    (l1 n).set j' (fill K' (Val (LitV (LitInt ((m : ℕ) : ℤ)))))
  let G : Fin (N + 1) → Fin (M + 1) → full_info_state × CPState := fun n m =>
    ([(cfg_to_cfg' ((l, s') : CPState), j), (cfg_to_cfg' ((l1 n, s') : CPState), j'),
      (cfg_to_cfg' ((l2 n m, s') : CPState), (l2 n m).length)], ((l2 n m, s') : CPState))
  let g1 : Fin ((N + 1) * (M + 1) - 1 + 1) → expr × state × List expr := fun n =>
    (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, [])
  have Hlim : osch_lim_exec (two_step_osch j j').fi_osch ([], ((l, s') : CPState)) =
      dunifP N ≫= fun n => dmap (G n) (dunifP M) :=
    two_step_osch_lim_exec j j' K K' N M ((l, s') : CPState) Hne Hsome Hsome'
  iexists (fun x y => ∃ n m, x = g1 (F (n, m)) ∧ y = G n m), two_step_osch j j', 0,
    (fun _ => ε), ε
  isplitr
  · ipureintro
    exact reducible_rand _ σ1
  isplitr
  · ipureintro
    exact fun _ => le_rfl
  isplitr
  · ipureintro
    rw [zero_add, Expval_const]
    exact mul_le_of_le_one_right zero_le (pmf_SeriesC _)
  isplitr
  · ipureintro
    rw [prim_step_rand_nat, Hdecomp, Hlim, dmap_dbind]
    refine ARcoupl_dbind' 0 0 0 _ _ _ _ (· = ·) _ (add_zero _).symm (fun n n' hn => ?_)
      (ARcoupl_eq _)
    subst hn
    rw [dmap_comp]
    apply ARcoupl_map
    exact ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      (fun m m' hm => ⟨n, m, rfl, by rw [hm]⟩) le_rfl (ARcoupl_eq _)
  isplitr
  · ipureintro
    rintro x1 x2 L y1 y2 ⟨n, m, rfl, h1⟩ ⟨n', m', rfl, h2⟩
    have hL1 : L = (G n m).1 := congrArg Prod.fst h1
    have hL2 : L = (G n' m').1 := congrArg Prod.fst h2
    have ha := congrArg (fun L : full_info_state => (L[1]?).map (fun q => q.1.1[j]?))
      (hL1.symm.trans hL2)
    simp only [G, l1, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, List.getElem?_set_self Hjl, Option.some.injEq] at ha
    have hnn : n = n' := Fin.ext (fill_lit_nat_inj K ha)
    subst hnn
    have hb := congrArg (fun L : full_info_state => (L[2]?).map (fun q => q.1.1[j']?))
      (hL1.symm.trans hL2)
    have Hjl'' : j' < (l1 n).length := by simpa [l1] using Hjl'
    simp only [G, l2, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, List.getElem?_set_self Hjl'', Option.some.injEq] at hb
    have hmm : m = m' := Fin.ext (fill_lit_nat_inj K' hb)
    subst hmm
    exact ⟨rfl, (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm⟩
  iintro %e2 %σ2 %efs %L %ρ2 %⟨n, m, h1, h2⟩
  simp only [g1, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
  beta_reduce
  imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))) $$ Hs Hj
    with ⟨Hs, Hj⟩
  imod spec_update_prog (l1 n) s' j' _ (fill K' (Val (LitV (LitInt ((m : ℕ) : ℤ))))) $$ Hs Hj'
    with ⟨Hs, Hj'⟩
  imodintro
  inext
  imod Hclose
  imodintro
  iframe Hσ Hs Hε
  isplitl
  · iapply wp_value'
    iapply HΦ $$ %(f n m)
    iexists (n : ℕ), (m : ℕ)
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 n.2
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 m.2
    isplitr
    · ipureintro
      rfl
    iframe Hj Hj'
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

open Classical in
/-- Rocq: `wp_couple_fragmented_rand_rand_inj`. Fragmented `rand N ~ rand M`, `N ≥ M`, under an
injective function `f` from `[0, M]` to `[0, N]`. -/
theorem wp_couple_fragmented_rand_rand_inj {M N : ℕ} (f : ℕ → ℕ) (Hinj : Function.Injective f)
    (j : ℕ) (K : List ectx_item) {s : Stuckness} {E : CoPset} (Hineq : M ≤ N)
    (Hdom : ∀ n : ℕ, n < M + 1 → f n < N + 1) :
    {{ j ⤇ fill K (Rand (Val (LitV (LitInt (M : ℤ)))) (Val (LitV LitUnit))) }}
      (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV LitUnit))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ));
      (iprop(⌜n ≤ N⌝ ∗
        ((∃ m : ℕ, ⌜m ≤ M⌝ ∗ ⌜f m = n⌝ ∗ j ⤇ fill K (Val (LitV (LitInt (m : ℤ))))) ∨
          (⌜¬ ∃ m : ℕ, m ≤ M ∧ f m = n⌝ ∗
            j ⤇ fill K (Rand (Val (LitV (LitInt (M : ℤ)))) (Val (LitV LitUnit)))))) :
        IProp GF) }} := by
  iintro %Φ Hr HΦ
  iapply wp_lift_step_prog_couple rfl
  simp only [foxtrotGS_spec_interp_eq]
  iintro %σ1 %⟨l, s'⟩ %ε ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree l s' j _ $$ Hs Hr
  have Hj : j < l.length := (List.getElem?_eq_some_iff.1 Hsome).1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  let g1 : Fin (N + 1) → expr × state × List expr := fun n =>
    (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, [])
  let Gacc : Fin (M + 1) → full_info_state × CPState := fun m' =>
    ([(cfg_to_cfg' ((l, s') : CPState), j),
      (cfg_to_cfg' ((l.set j (fill K (Val (LitV (LitInt ((m' : ℕ) : ℤ))))), s') : CPState),
        l.length)],
      ((l.set j (fill K (Val (LitV (LitInt ((m' : ℕ) : ℤ))))), s') : CPState))
  let Grej : Fin (N + 1) → full_info_state × CPState := fun n =>
    ([(cfg_to_cfg' ((l, s') : CPState), l.length + (n : ℕ))], ((l, s') : CPState))
  have Hlim : osch_lim_exec (frag_osch M N f j l.length).fi_osch ([], ((l, s') : CPState)) =
      dunifP N ≫= fun n : Fin (N + 1) =>
        if ∃ m : ℕ, m ≤ M ∧ f m = (n : ℕ) then dmap Gacc (dunifP M) else dret (Grej n) :=
    frag_osch_lim_exec M N f j K ((l, s') : CPState) Hsome
  let S : expr × state × List expr → full_info_state × CPState → Prop := fun x y =>
    ∃ n : Fin (N + 1), x = g1 n ∧
      ((∃ m' : Fin (M + 1), f m' = n ∧ y = Gacc m') ∨
        ((¬ ∃ m : ℕ, m ≤ M ∧ f m = (n : ℕ)) ∧ y = Grej n))
  iexists S, frag_osch M N f j l.length, 0, (fun _ => ε), ε
  isplitr
  · ipureintro
    exact reducible_rand _ σ1
  isplitr
  · ipureintro
    exact fun _ => le_rfl
  isplitr
  · ipureintro
    rw [zero_add, Expval_const]
    exact mul_le_of_le_one_right zero_le (pmf_SeriesC _)
  isplitr
  · ipureintro
    have HL : prim_step (Λ := con_prob_lang)
        (Rand (Val (LitV (LitInt (N : ℤ)))) (Val (LitV LitUnit))) σ1 =
        dunifP N ≫= fun n : Fin (N + 1) => dmap g1 (if ∃ m : Fin (M + 1), f m = (n : ℕ) then
          dmap (fun m' : Fin (M + 1) => (⟨f m', Hdom _ m'.isLt⟩ : Fin (N + 1))) (dunifP M)
        else dret n) := by
      rw [prim_step_rand_nat]
      conv_lhs => rw [dunif_fragmented N M f Hinj Hdom Hineq]
      exact dmap_dbind _ _ _
    rw [HL]
    refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl)
      (fun b => (congrArg (fun μ => μ b) Hlim).symm) (fun _ _ h => h) le_rfl ?_
    refine ARcoupl_dbind' 0 0 0 _ _ _ _ (· = ·) S (add_zero _).symm (fun n n' hn => ?_)
      (ARcoupl_eq (dunifP N))
    · subst hn
      have hiff : (∃ m : Fin (M + 1), f m = (n : ℕ)) ↔ ∃ m : ℕ, m ≤ M ∧ f m = (n : ℕ) :=
        ⟨fun ⟨m, hm⟩ => ⟨m, Nat.lt_succ_iff.1 m.2, hm⟩,
          fun ⟨m, hm, hfm⟩ => ⟨⟨m, Nat.lt_succ_iff.2 hm⟩, hfm⟩⟩
      by_cases h : ∃ m : ℕ, m ≤ M ∧ f m = (n : ℕ)
      · simp only [hiff.2 h, h, ↓reduceIte]
        rw [dmap_comp]
        apply ARcoupl_map
        refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ?_ le_rfl
          (ARcoupl_eq (dunifP M))
        rintro m' m'' rfl
        obtain ⟨m, -, hm⟩ := h
        refine ⟨⟨f m', Hdom _ m'.isLt⟩, rfl, Or.inl ⟨m', rfl, rfl⟩⟩
      · have h' : ¬ ∃ m : Fin (M + 1), f m = (n : ℕ) := fun h' => h (hiff.1 h')
        simp only [h', h, ↓reduceIte, dmap_dret]
        exact ARcoupl_dret _ _ S _ ⟨n, rfl, Or.inr ⟨h, rfl⟩⟩
  isplitr
  · ipureintro
    rintro x1 x2 L y1 y2 ⟨n1, rfl, h1⟩ ⟨n2, rfl, h2⟩
    have key : ∀ {n : Fin (N + 1)} {y : CPState},
        ((∃ m' : Fin (M + 1), f m' = n ∧ (L, y) = Gacc m') ∨
          ((¬ ∃ m : ℕ, m ≤ M ∧ f m = (n : ℕ)) ∧ (L, y) = Grej n)) →
        ((∃ m' : Fin (M + 1), f m' = n ∧ L = (Gacc m').1 ∧ y = (Gacc m').2) ∨
          (L = (Grej n).1 ∧ y = (Grej n).2)) := by
      rintro n y (⟨m', hm', h⟩ | ⟨-, h⟩)
      · exact Or.inl ⟨m', hm', congrArg Prod.fst h, congrArg Prod.snd h⟩
      · exact Or.inr ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    rcases key h1 with ⟨m1, hm1, hL1, hy1⟩ | ⟨hL1, hy1⟩ <;>
      rcases key h2 with ⟨m2, hm2, hL2, hy2⟩ | ⟨hL2, hy2⟩
    · have ha := congrArg (fun L : full_info_state => (L[1]?).map (fun q => q.1.1[j]?))
        (hL1.symm.trans hL2)
      simp only [Gacc, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.map_some, List.getElem?_set_self Hj, Option.some.injEq] at ha
      have hm : m1 = m2 := Fin.ext (fill_lit_nat_inj K ha)
      subst hm
      have hn : n1 = n2 := Fin.ext (hm1.symm.trans hm2)
      subst hn
      exact ⟨rfl, hy1.trans hy2.symm⟩
    · have := congrArg List.length (hL1.symm.trans hL2)
      simp [Gacc, Grej] at this
    · have := congrArg List.length (hL1.symm.trans hL2)
      simp [Gacc, Grej] at this
    · have ha := congrArg (fun L : full_info_state => (L[0]?).map Prod.snd)
        (hL1.symm.trans hL2)
      simp only [Grej, List.getElem?_cons_zero, Option.map_some, Option.some.injEq,
        Nat.add_left_cancel_iff] at ha
      have hn : n1 = n2 := Fin.ext ha
      subst hn
      exact ⟨rfl, hy1.trans hy2.symm⟩
  iintro %e2 %σ2 %efs %L %ρ2 %⟨n, h1, h2⟩
  simp only [g1, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  rcases h2 with ⟨m', hm', h2⟩ | ⟨hrej, h2⟩
  · -- we step on an accepted value
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    beta_reduce
    imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((m' : ℕ) : ℤ))))) $$ Hs Hr
      with ⟨Hs, Hr⟩
    imodintro
    inext
    imod Hclose
    imodintro
    iframe Hσ Hs Hε
    isplitl
    · iapply wp_value'
      iapply HΦ $$ %(n : ℕ)
      isplitr
      · ipureintro
        exact Nat.lt_succ_iff.1 n.2
      ileft
      iexists (m' : ℕ)
      isplitr
      · ipureintro
        exact Nat.lt_succ_iff.1 m'.2
      isplitr
      · ipureintro
        exact hm'
      iexact Hr
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  · -- we reject this value
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    beta_reduce
    imodintro
    inext
    imod Hclose
    imodintro
    iframe Hσ Hs Hε
    isplitl
    · iapply wp_value'
      iapply HΦ $$ %(n : ℕ)
      isplitr
      · ipureintro
        exact Nat.lt_succ_iff.1 n.2
      iright
      isplitr
      · ipureintro
        exact hrej
      iexact Hr
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro

open Classical in
/-- Rocq: `pupd_couple_fragmented_tape_rand_inj_rev'`. Fragmented state rand `N ~ rand M`,
`M ≥ N`, under an injective function `f` from `[0, N]` to `[0, M]`, but with errors for
rejection sampling. -/
theorem pupd_couple_fragmented_tape_rand_inj_rev' {M N : ℕ} (f : ℕ → ℕ)
    (Hinj : Function.Injective f) (ns : List ℕ) (α : Loc) (j : ℕ) (K : List ectx_item)
    (E : CoPset) (ε : ℝ≥0∞) (Hineq : N < M) (Hdom : ∀ n : ℕ, n < N + 1 → f n < M + 1) :
    ▷ α ↪N (N; ns) ⊢@{IProp GF} ↯ ε -∗
      j ⤇ fill K (Rand (Val (LitV (LitInt (M : ℤ)))) (Val (LitV LitUnit))) -∗
      pupd E E iprop(∃ m : ℕ, ⌜m ≤ M⌝ ∗ j ⤇ fill K (Val (LitV (LitInt (m : ℤ)))) ∗
        ((∃ n : ℕ, ⌜n ≤ N⌝ ∗ ⌜f n = m⌝ ∗ α ↪N (N; ns ++ [n])) ∨
          (⌜¬ ∃ n : ℕ, n ≤ N ∧ f n = m⌝ ∗ α ↪N (N; ns) ∗
            ↯ (((M + 1 : ℕ) : ℝ≥0∞) / (((M + 1 : ℕ) : ℝ≥0∞) - ((N + 1 : ℕ) : ℝ≥0∞)) * ε)))) := by
  unfold pupd pupd_def
  simp only [foxtrotGS_state_interp_eq, foxtrotGS_spec_interp_eq, foxtrotGS_err_interp_eq]
  iintro Hα Herr Hr %σ %⟨l, s'⟩ %εnow ⟨⟨Hh, Ht⟩, Hs, Hε⟩
  imod Hα
  iunfold nat_tape at Hα
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  unfold tapes_auth
  icombine Ht Hα gives %H
  rw [ext_get?_eq] at H
  ihave %Hlookup := spec_auth_prog_agree l s' j _ $$ Hs Hr
  ihave %Hle := ErrorCredit.supply_bound $$ Hε Herr
  have Hj : j < l.length := (List.getElem?_eq_some_iff.1 Hlookup).1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  let δ : ℝ≥0∞ := ε * ((N + 1 : ℕ) : ℝ≥0∞) / ((M - N : ℕ) : ℝ≥0∞)
  let E2 : CPState → ℝ≥0∞ := fun ρ =>
    if ∃ n : Fin (N + 1), ρ.1[j]? = some (fill K (Val (LitV (LitInt ((f n : ℕ) : ℤ)))))
    then εnow - ε else εnow + δ
  let g : Fin (M + 1) → CPState := fun m =>
    ((l.set j (fill K (Val (LitV (LitInt ((m : ℕ) : ℤ))))), s') : CPState)
  let k : CPState → full_info_state × CPState := fun ρ' =>
    ([(cfg_to_cfg' ((l, s') : CPState), j), (cfg_to_cfg' ρ', ρ'.1.length)], ρ')
  let F : Fin (N + 1) → Fin (M + 1) := fun n => ⟨f n, Hdom n n.2⟩
  let upd : Fin (N + 1) → state := fun n => state_upd_tapes (·.insert α ⟨N, fs ++ [n]⟩) σ
  have hE2 : ∀ m, E2 (g m) =
      if ∃ n : Fin (N + 1), f n = (m : ℕ) then εnow - ε else εnow + δ := by
    intro m
    have hiff : (∃ n : Fin (N + 1),
        (g m).1[j]? = some (fill K (Val (LitV (LitInt ((f n : ℕ) : ℤ)))))) ↔
        ∃ n : Fin (N + 1), f n = (m : ℕ) := by
      simp only [g, List.getElem?_set_self Hj, Option.some.injEq]
      exact ⟨fun ⟨n, h⟩ => ⟨n, (fill_lit_nat_inj K h).symm⟩, fun ⟨n, h⟩ => ⟨n, by rw [h]⟩⟩
    exact if_congr hiff rfl rfl
  have Hlim : osch_lim_exec (full_info_one_step_stutter_osch j).fi_osch ([], ((l, s') : CPState)) =
      dmap (k ∘ g) (dunifP M) :=
    (full_info_one_step_stutter_osch_lim_exec j _).trans
      ((congrArg (dmap _) (step'_fill_rand_nat j ((l, s') : CPState) K M Hlookup)).trans
        (dmap_comp _ _ _))
  have hkg : ∀ m1 m2 : Fin (M + 1), (k (g m1)).1 = (k (g m2)).1 → m1 = m2 := by
    intro m1 m2 h
    have ha := congrArg (fun L : full_info_state => (L[1]?).map (fun q => q.1.1[j]?)) h
    simp only [k, g, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, List.getElem?_set_self Hj, Option.some.injEq] at ha
    exact Fin.ext (fill_lit_nat_inj K ha)
  let S : state → full_info_state × CPState → Prop := fun σ' y =>
    (∃ n : Fin (N + 1), σ' = upd n ∧ y = k (g (F n))) ∨
      (∃ m : Fin (M + 1), (¬ ∃ n : Fin (N + 1), f n = (m : ℕ)) ∧ σ' = σ ∧ y = k (g m))
  iapply spec_coupl_rec σ ((l, s') : CPState) εnow _
  iexists S, (dunifP M ≫= fun m : Fin (M + 1) =>
      if decide (∃ n : Fin (N + 1), f n = (m : ℕ)) then con_prob_lang.state_step σ α else dret σ),
    full_info_one_step_stutter_osch j, 0, (fun p => E2 p.2), max (εnow - ε) (εnow + δ)
  isplitr
  · ipureintro
    have H1 := state_step_sch_erasable σ α ⟨N, fs⟩ H
    have H2 := dret_sch_erasable (Λ := con_prob_lang) σ tape_oblivious_sch
    exact sch_erasable_dbind_predicate (Λ := con_prob_lang) tape_oblivious_sch (dunifP M)
      (con_prob_lang.state_step σ α) (dret σ) σ
      (fun m : Fin (M + 1) => decide (∃ n : Fin (N + 1), f n = (m : ℕ)))
      (dunifP_mass M) H1 H2
  isplitr
  · ipureintro
    intro y
    show E2 y.2 ≤ _
    simp only [E2]
    split
    · exact le_max_left _ _
    · exact le_max_right _ _
  isplitr
  · ipureintro
    rw [zero_add, Hlim, Expval_dmap]
    refine le_of_eq ?_
    unfold Expval
    rw [← frag_expval_calc M N f Hinj Hdom Hineq εnow ε Hle]
    exact tsum_congr fun m => congrArg _ (hE2 m)
  isplitr
  · ipureintro
    have HR : dmap (k ∘ g) (dunifP M) = dunifP M ≫= fun m : Fin (M + 1) =>
        dmap (k ∘ g) (if ∃ n : Fin (N + 1), f n = (m : ℕ) then dmap F (dunifP N) else dret m) := by
      conv_lhs => rw [dunif_fragmented M N f Hinj Hdom Hineq.le]
      exact dmap_dbind _ _ _
    refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl)
      (fun b => (congrArg (fun μ => μ b) (Hlim.trans HR)).symm) (fun _ _ h => h) le_rfl ?_
    refine ARcoupl_dbind' 0 0 0 _ _ _ _ (· = ·) S (add_zero _).symm (fun m m' hm => ?_)
      (ARcoupl_eq (dunifP M))
    subst hm
    by_cases h : ∃ n : Fin (N + 1), f n = (m : ℕ)
    · simp only [h, _root_.decide_true, ↓reduceIte]
      rw [state_step_unfold σ α N fs H, dmap_comp]
      apply ARcoupl_map
      refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ?_ le_rfl
        (ARcoupl_eq (dunifP N))
      rintro n n' rfl
      exact Or.inl ⟨n, rfl, rfl⟩
    · simp only [h, _root_.decide_false, Bool.false_eq_true, ↓reduceIte, dmap_dret]
      exact ARcoupl_dret _ _ S _ (Or.inr ⟨m, h, rfl, rfl⟩)
  isplitr
  · ipureintro
    have key : ∀ {σ' : state} {L : full_info_state} {ρ : CPState}, S σ' (L, ρ) →
        ∃ m : Fin (M + 1), L = (k (g m)).1 ∧ ρ = (k (g m)).2 ∧
          ((∃ n : Fin (N + 1), F n = m ∧ σ' = upd n) ∨
            ((¬ ∃ n : Fin (N + 1), f n = (m : ℕ)) ∧ σ' = σ)) := by
      rintro σ' L ρ (⟨n, rfl, h⟩ | ⟨m, hm, rfl, h⟩)
      · exact ⟨F n, congrArg Prod.fst h, congrArg Prod.snd h, Or.inl ⟨n, rfl, rfl⟩⟩
      · exact ⟨m, congrArg Prod.fst h, congrArg Prod.snd h, Or.inr ⟨hm, rfl⟩⟩
    rintro σx σy ρx ρy L hx hy
    obtain ⟨m1, hL1, hρ1, h1⟩ := key hx
    obtain ⟨m2, hL2, hρ2, h2⟩ := key hy
    have hm := hkg m1 m2 (hL1.symm.trans hL2)
    subst hm
    refine ⟨?_, hρ1.trans hρ2.symm⟩
    rcases h1 with ⟨n1, hn1, rfl⟩ | ⟨hn1, rfl⟩ <;> rcases h2 with ⟨n2, hn2, rfl⟩ | ⟨hn2, rfl⟩
    · have : n1 = n2 := Fin.ext (Hinj (congrArg Fin.val (hn1.trans hn2.symm)))
      rw [this]
    · exact absurd ⟨n1, congrArg Fin.val hn1⟩ hn2
    · exact absurd ⟨n2, congrArg Fin.val hn2⟩ hn1
    · rfl
  iintro %σ2 %L %ρ' %HS
  rcases HS with ⟨n, rfl, h⟩ | ⟨m, hm, rfl, h⟩
  · -- accepted
    have hρ : ρ' = g (F n) := congrArg Prod.snd h
    subst hρ
    have hX : E2 (g (F n)) = εnow - ε := by
      rw [hE2]
      simp only [show ∃ n' : Fin (N + 1), f n' = ((F n : Fin (M + 1)) : ℕ) from ⟨n, rfl⟩,
        ↓reduceIte]
    beta_reduce
    simp only [hX]
    imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((f n : ℕ) : ℤ))))) $$ Hs Hr
      with ⟨Hs, Hr⟩
    imod ghost_map_update (⟨N, fs ++ [n]⟩ : tape) $$ Ht Hα with ⟨Ht, Hα⟩
    rw [ext_insert_eq]
    imod ErrorCredit.supply_decrease $$ Hε Herr with Hε
    imodintro
    iapply spec_coupl_ret_pair (upd n) (l.set j (fill K (Val (LitV (LitInt ((f n : ℕ) : ℤ))))))
      s' _ (εnow - ε)
    imod Hclose
    imodintro
    simp only [upd, state_upd_tapes_heap', state_upd_tapes_tapes]
    iframe Hh Ht Hs Hε
    iexists f n
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 (Hdom n n.2)
    iframe Hr
    ileft
    iexists (n : ℕ)
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 n.2
    isplitr
    · ipureintro
      rfl
    iunfold nat_tape
    iexists fs ++ [n]
    iframe Hα
    ipureintro
    simp [Hfs]
  · -- rejected
    have hρ : ρ' = g m := congrArg Prod.snd h
    subst hρ
    have hX : E2 (g m) = εnow + δ := by
      rw [hE2]
      simp only [hm, ↓reduceIte]
    beta_reduce
    simp only [hX]
    imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((m : ℕ) : ℤ))))) $$ Hs Hr
      with ⟨Hs, Hr⟩
    by_cases h1 : 1 ≤ εnow + δ
    · imodintro
      iapply spec_coupl_ret_err_ge_1 _ _ _ _ h1
    imodintro
    iapply spec_coupl_ret_pair _ (l.set j (fill K (Val (LitV (LitInt ((m : ℕ) : ℤ)))))) s' _
      (εnow + δ)
    imod ErrorCredit.supply_increase (ε₂ := δ) (lt_of_not_ge h1) $$ Hε with ⟨Hε, Hδ⟩
    icombine Herr Hδ as Herr
    imod Hclose
    imodintro
    iframe Hh Ht Hs Hε
    iexists (m : ℕ)
    isplitr
    · ipureintro
      exact Nat.lt_succ_iff.1 m.2
    iframe Hr
    iright
    isplitr
    · ipureintro
      rintro ⟨n, hn, hfn⟩
      exact hm ⟨⟨n, Nat.lt_succ_iff.2 hn⟩, hfn⟩
    isplitl [Hα]
    · iunfold nat_tape
      iexists fs
      iframe Hα
      ipureintro
      exact Hfs
    · iapply ErrorCredit.ext (frag_err_eq M N Hineq ε) $$ Herr

end rules

end Foxtrot
