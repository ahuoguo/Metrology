module

public import Metrology.Foxtrot.CouplingRules

/-!
# Coupling rules of Foxtrot (associativity, toss, tapes, labels)

Ported from clutch/theories/foxtrot/coupling_rules.v (lines 2968–4134).

## Rocq → Lean name map
All ported lemmas keep their Rocq names:
* `pupd_couple_associativity {p q r s x y} α β ns ns' j K j' K' E Hpq Hrs hx hy`
* `wp_couple_toss {x y k} j K {s E} Hk hx`
* `pupd_couple_tape_rand N f Hbij K E α z ns j hN Hdom`
* `pupd_couple_two_tapes_rand N M f K E α α' z z' x ns ms j hN hM hx Hcond1 Hcond2 Hcond3`
* `wp_couple_rand_rand_lbl N f Hbij z K {s E} α j hN Hdom`
* `wp_couple_rand_lbl_rand_lbl N f Hbij z K {s E} α α' j hN Hdom`
* `wp_couple_rand_lbl_rand_lbl_wrong N M f Hbij z K {s E} α α' xs ys j hN Hneq Hdom`

## Deviations
* Rocq `Bij nat nat f` instances become explicit `(Hbij : Function.Bijective f)`, and
  `restr_bij_fin` is inlined: the restriction `ff : Fin (N+1) → Fin (N+1)` is bijective via
  `Finite.injective_iff_bijective`.
* `TCEq N (Z.to_nat z)` becomes `(hN : N = z.toNat)`. Rocq `-∗` chains become `⊢ … -∗ …`.
* Rocq `bool_decide (a < b)` in the postcondition of `pupd_couple_associativity` becomes a
  Lean `if a < b then … else …` (decidable `Prop`).
* Schedulers that Rocq builds inline are named helpers: `toss_osch` (for `wp_couple_toss`).
  The arithmetic of the associativity bijection is factored into `assoc_f`, `assoc_f_regions`,
  `assoc_f_lt`, `assoc_f_inj`, `assoc_post` and `assoc_pos`. The common coupling step of the
  three `*_lbl` rules is `prog_coupl_unif_unif`.
* Other local helpers (not in Rocq): `dbind_dmap_left`, `state_step_two_unfold`,
  `state_step_two_sch_erasable`, `head_step_rand_lbl_empty`, `head_step_rand_lbl_wrong`,
  `step'_fill_unif`, `prim_step_rand_lbl`, `mul_add_div_of_lt`, `mul_add_mod_of_lt`,
  `nat_mul_add_inj` (Rocq `Nat.mul_split_l`), `toss_inner_lim_exec`, `toss_osch_lim_exec`,
  `assoc_split`, and the instance `nat_spec_tape_timeless`.
* Commented-out Rocq lemmas in this range are skipped.
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

/-- Helper: binding after a `dmap` (Rocq: `dbind_assoc'` + `dret_id_left`). -/
theorem dbind_dmap_left {A B C : Type} [Countable A] [Countable B] [Countable C]
    (f : A → B) (μ : Distr A) (h : B → Distr C) :
    (dmap f μ ≫= h) = μ ≫= fun a => h (f a) := by
  rw [dmap, ← dbind_assoc]; simp only [dret_id_left]

/-- Helper: sampling the two tapes `α` and `α'` (Rocq: inline, `state_step` +
`lookup_insert_ne`). -/
theorem state_step_two_unfold (σ : state) (α α' : Loc) (N M : ℕ) (fs : List (Fin (N + 1)))
    (fs' : List (Fin (M + 1))) (H : σ.tapes[α]? = some ⟨N, fs⟩)
    (H' : σ.tapes[α']? = some ⟨M, fs'⟩) (hne : α ≠ α') :
    (con_prob_lang.state_step σ α ≫= fun σ' => con_prob_lang.state_step σ' α') =
      dunifP N ≫= fun n => dmap (fun m => state_upd_tapes (·.insert α' ⟨M, fs' ++ [m]⟩)
        (state_upd_tapes (·.insert α ⟨N, fs ++ [n]⟩) σ)) (dunifP M) := by
  rw [state_step_unfold σ α N fs H, dbind_dmap_left]
  refine dbind_ext_right _ _ _ fun n => ?_
  refine state_step_unfold _ α' M fs' ?_
  simp only [state_upd_tapes_tapes, map_getElem?_insert_ne _ _ _ _ hne, H']

/-- Helper: sampling the two tapes `α` and `α'` is erasable (Rocq: inline,
`sch_erasable_dbind` + `state_step_sch_erasable`). -/
theorem state_step_two_sch_erasable (σ : state) (α α' : Loc) (N M : ℕ)
    (fs : List (Fin (N + 1))) (fs' : List (Fin (M + 1))) (H : σ.tapes[α]? = some ⟨N, fs⟩)
    (H' : σ.tapes[α']? = some ⟨M, fs'⟩) (hne : α ≠ α') :
    sch_erasable tape_oblivious_sch
      (con_prob_lang.state_step σ α ≫= fun σ' => con_prob_lang.state_step σ' α') σ := by
  refine sch_erasable_dbind _ _ _ _ (state_step_sch_erasable σ α _ H) fun σ' hσ' => ?_
  rw [state_step_unfold σ α N fs H, dmap_pos] at hσ'
  obtain ⟨n, rfl, -⟩ := hσ'
  refine state_step_sch_erasable _ α' ⟨M, fs'⟩ ?_
  simp only [state_upd_tapes_tapes, map_getElem?_insert_ne _ _ _ _ hne, H']

/-- Helper: `rand(#lbl:α) #z` on an allocated empty tape of the right bound samples uniformly. -/
theorem head_step_rand_lbl_empty (z : ℤ) (α : Loc) (σ : state)
    (H : σ.tapes[α]? = some ⟨z.toNat, []⟩) :
    head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) σ =
      dmap (fun n : Fin (z.toNat + 1) =>
        ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) : expr × state × List expr))
        (dunifP z.toNat) := by
  simp [head_step, H]

/-- Helper: `rand(#lbl:α) #z` on a tape of a different bound samples uniformly. -/
theorem head_step_rand_lbl_wrong (z : ℤ) (α : Loc) (σ : state) (M : ℕ)
    (ms : List (Fin (M + 1))) (H : σ.tapes[α]? = some ⟨M, ms⟩) (hne : M ≠ z.toNat) :
    head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) σ =
      dmap (fun n : Fin (z.toNat + 1) =>
        ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) : expr × state × List expr))
        (dunifP z.toNat) := by
  simp [head_step, H, hne]

/-- Helper: one step of the RHS thread `j` running `fill K e`, where `e` samples uniformly
without touching the state. -/
theorem step'_fill_unif (j : ℕ) (ρ : CPState) (K : List ectx_item) (e : expr) (Z : ℕ)
    (Hsome : ρ.1[j]? = some (fill K e))
    (Hhead : head_step e ρ.2 = dmap (fun n : Fin (Z + 1) =>
        ((Val (LitV (LitInt ((n : ℕ) : ℤ))), ρ.2, []) : expr × state × List expr))
        (dunifP Z)) :
    step' j ρ =
      dmap (fun n : Fin (Z + 1) =>
        ((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), ρ.2) : CPState))
        (dunifP Z) := by
  have hpos : 0 < head_step e ρ.2 ((Val (LitV (LitInt ((0 : ℕ) : ℤ))), ρ.2, []) :
      expr × state × List expr) := by
    rw [Hhead, dmap_pos]
    exact ⟨0, rfl, dunifP_pos _ _⟩
  have Hval : ConProbLang.to_val (Λ := con_prob_lang) (fill K e) = none :=
    conEctxiLanguage.fill_not_val (Λ := con_prob_ectxi_lang) K _ (val_head_stuck e ρ.2 _ hpos)
  simp only [step', Hsome, Hval]
  rw [prim_step_fill_head K e ρ.2 _ _ Hhead (dunifP_mass _)]
  refine (dmap_comp (β := expr × state × List expr) (δ := CPState) _ _ _).trans ?_
  congr 1
  funext n
  simp [Function.comp]

/-- Helper: the `prim_step` of a uniformly sampling `rand(#lbl:α) #z`. -/
theorem prim_step_rand_lbl (z : ℤ) (α : Loc) (σ : state)
    (Hhead : head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) σ =
      dmap (fun n : Fin (z.toNat + 1) =>
        ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) : expr × state × List expr))
        (dunifP z.toNat)) :
    prim_step (Λ := con_prob_lang) (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) σ =
      dmap (fun n : Fin (z.toNat + 1) =>
        ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) : expr × state × List expr))
        (dunifP z.toNat) :=
  prim_step_fill_head [] _ σ _ _ Hhead (dunifP_mass _)

/-- Helper: `(a * k + b) / k = a` for `b < k`. -/
theorem mul_add_div_of_lt {k a b : ℕ} (hb : b < k) : (a * k + b) / k = a := by
  rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]

/-- Helper: `(a * k + b) % k = b` for `b < k`. -/
theorem mul_add_mod_of_lt {k a b : ℕ} (hb : b < k) : (a * k + b) % k = b := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

/-- Helper (Rocq: `Nat.mul_split_l`): `a * k + b` determines `a` and `b < k`. -/
theorem nat_mul_add_inj {k a b c d : ℕ} (hb : b < k) (hd : d < k) (h : a * k + b = c * k + d) :
    a = c ∧ b = d := by
  constructor
  · rw [← mul_add_div_of_lt (a := a) hb, h, mul_add_div_of_lt hd]
  · rw [← mul_add_mod_of_lt (a := a) hb, h, mul_add_mod_of_lt hd]

/-- Helper: the full-information scheduler of `wp_couple_toss` (Rocq: inline). It steps thread
`j` and then records a uniform sample `m ≤ k - 1` by stuttering on the out-of-bounds thread
`m + len`. -/
def toss_osch (j len k : ℕ) : full_info_oscheduler :=
  full_info_cons_osch (fun _ => dret j) (fun _ =>
    full_info_cons_osch (fun _ => dmap (fun m : Fin (k - 1 + 1) => (m : ℕ) + len) (dunifP (k - 1)))
      (fun _ => full_info_inhabitant))

/-- Helper: the second part of `toss_osch` (Rocq: inline in `wp_couple_toss`). -/
theorem toss_inner_lim_exec (k len : ℕ) (ρ : CPState) (h : ρ.1.length = len) :
    osch_lim_exec (full_info_cons_osch
      (fun _ => dmap (fun m : Fin (k - 1 + 1) => (m : ℕ) + len) (dunifP (k - 1)))
      (fun _ => full_info_inhabitant)).fi_osch ([], ρ) =
      dmap (fun m : Fin (k - 1 + 1) =>
        (([(cfg_to_cfg' ρ, (m : ℕ) + len)] : full_info_state), ρ)) (dunifP (k - 1)) := by
  rw [full_info_cons_osch_lim_exec, dbind_dmap_left]
  refine dbind_ext_right _ _ _ fun m => ?_
  rw [out_of_bounds_step' _ _ (by omega), dret_id_left]
  have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, (m : ℕ) + len)] full_info_inhabitant [] ρ
  simp only [List.append_nil] at this
  rw [this, full_info_inhabitant_lim_exec, dmap_dret]
  rfl

/-- Helper: the limit execution of `toss_osch` (Rocq: inline in `wp_couple_toss`). -/
theorem toss_osch_lim_exec (j k : ℕ) (K : List ectx_item) (y : ℕ) (ρ : CPState)
    (Hsome : ρ.1[j]? = some (fill K (Rand (Val (LitV (LitInt (y : ℤ)))) (Val (LitV LitUnit))))) :
    osch_lim_exec (toss_osch j ρ.1.length k).fi_osch ([], ρ) =
      dunifP y ≫= fun n : Fin (y + 1) => dmap (fun m : Fin (k - 1 + 1) =>
        (([(cfg_to_cfg' ρ, j),
          (cfg_to_cfg' ((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), ρ.2) : CPState),
            (m : ℕ) + ρ.1.length)] : full_info_state),
          ((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), ρ.2) : CPState)))
        (dunifP (k - 1)) := by
  unfold toss_osch
  rw [full_info_cons_osch_lim_exec, dret_id_left, step'_fill_rand_nat j ρ K y Hsome, dmap]
  refine (dbind_assoc (β := CPState) _ _ _).symm.trans ?_
  refine dbind_ext_right _ _ _ fun n => ?_
  refine (dret_id_left (α := CPState) _ _).trans ?_
  have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, j)]
    (full_info_cons_osch (fun _ => dmap (fun m : Fin (k - 1 + 1) => (m : ℕ) + ρ.1.length)
      (dunifP (k - 1))) (fun _ => full_info_inhabitant)) []
    ((ρ.1.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), ρ.2) : CPState)
  simp only [List.append_nil] at this
  refine this.trans ?_
  refine (congrArg (dmap _) (toss_inner_lim_exec k ρ.1.length _ (by simp))).trans ?_
  rw [dmap_comp]
  rfl

/-! ### Arithmetic of `pupd_couple_associativity` -/

/-- Helper (Rocq: `f'` in `pupd_couple_associativity`): the bijection
`[0, s] × [0, q] → [0, (q+1)(s+1) - 1]` mapping the region `a < r ∧ c < p` onto `[0, p r)`,
the region `a < r ∧ p ≤ c` onto `[p r, r (q+1))` and the region `r ≤ a` onto
`[r (q+1), (q+1)(s+1))`. (The parameter `s` is not used; it is kept for readability.) -/
def assoc_f (p q r : ℕ) (a c : ℕ) : ℕ :=
  if a < r ∧ c < p then a * p + c
  else if a < r then p * r + (c - p) * r + a
  else r * (q + 1) + (a - r) * (q + 1) + c

/-- Helper: `p r + r (q + 1 - p) = r (q + 1)`. -/
theorem assoc_split (p q r : ℕ) (Hpq : p ≤ q + 1) : p * r + r * (q + 1 - p) = r * (q + 1) := by
  rw [Nat.mul_comm p r, ← Nat.mul_add]
  congr 1
  omega

/-- Helper: the three regions of `assoc_f`. -/
theorem assoc_f_regions (p q r s a c : ℕ) (Hpq : p ≤ q + 1) (_Hrs : r ≤ s + 1)
    (ha : a < s + 1) (hc : c < q + 1) :
    ((a < r ∧ c < p) → assoc_f p q r a c < p * r) ∧
    ((a < r ∧ p ≤ c) → p * r ≤ assoc_f p q r a c ∧ assoc_f p q r a c < r * (q + 1)) ∧
    (r ≤ a → r * (q + 1) ≤ assoc_f p q r a c ∧ assoc_f p q r a c < (q + 1) * (s + 1)) := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_, fun h1 => ?_⟩
  · simp only [assoc_f, h1, h2, and_self, ↓reduceIte]
    have : a * p + c < (a + 1) * p := by rw [add_mul, one_mul]; omega
    exact lt_of_lt_of_le this (by rw [Nat.mul_comm p r]; exact Nat.mul_le_mul_right _ h1)
  · have h2' : ¬ c < p := by omega
    simp only [assoc_f, h1, h2', and_false, ↓reduceIte]
    refine ⟨by omega, ?_⟩
    have : p * r + (c - p) * r + a < p * r + (c - p + 1) * r := by rw [add_mul, one_mul]; omega
    refine lt_of_lt_of_le this ?_
    rw [← assoc_split p q r Hpq, Nat.mul_comm r]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  · have h1' : ¬ a < r := by omega
    simp only [assoc_f, h1', false_and, ↓reduceIte]
    refine ⟨by omega, ?_⟩
    have : r * (q + 1) + (a - r) * (q + 1) + c < (a + 1) * (q + 1) := by
      rw [← Nat.add_mul r (a - r) (q + 1), add_mul a 1, one_mul]
      have : r + (a - r) = a := by omega
      rw [this]; omega
    refine lt_of_lt_of_le this ?_
    rw [Nat.mul_comm (q + 1)]
    exact Nat.mul_le_mul_right _ ha

/-- Helper: `assoc_f` is bounded by `(q + 1) (s + 1)`. -/
theorem assoc_f_lt (p q r s a c : ℕ) (Hpq : p ≤ q + 1) (Hrs : r ≤ s + 1)
    (ha : a < s + 1) (hc : c < q + 1) : assoc_f p q r a c < (q + 1) * (s + 1) := by
  obtain ⟨HA, HB, HC⟩ := assoc_f_regions p q r s a c Hpq Hrs ha hc
  have H1 : p * r ≤ r * (q + 1) := by
    rw [Nat.mul_comm p]; exact Nat.mul_le_mul_left _ Hpq
  have H2 : r * (q + 1) ≤ (q + 1) * (s + 1) := by
    rw [Nat.mul_comm r]; exact Nat.mul_le_mul_left _ Hrs
  by_cases h1 : a < r
  · by_cases h2 : c < p
    · exact lt_of_lt_of_le (HA ⟨h1, h2⟩) (H1.trans H2)
    · exact lt_of_lt_of_le (HB ⟨h1, by omega⟩).2 H2
  · exact (HC (by omega)).2

/-- Helper: `assoc_f` is injective on `[0, s] × [0, q]`. -/
theorem assoc_f_inj (p q r s a c a' c' : ℕ) (Hpq : p ≤ q + 1) (Hrs : r ≤ s + 1)
    (ha : a < s + 1) (hc : c < q + 1) (ha' : a' < s + 1) (hc' : c' < q + 1)
    (h : assoc_f p q r a c = assoc_f p q r a' c') : a = a' ∧ c = c' := by
  obtain ⟨HA, HB, HC⟩ := assoc_f_regions p q r s a c Hpq Hrs ha hc
  obtain ⟨HA', HB', HC'⟩ := assoc_f_regions p q r s a' c' Hpq Hrs ha' hc'
  have H1 : p * r ≤ r * (q + 1) := by
    rw [Nat.mul_comm p]; exact Nat.mul_le_mul_left _ Hpq
  by_cases h1 : a < r <;> by_cases h2 : c < p <;> by_cases h1' : a' < r <;>
    by_cases h2' : c' < p
  all_goals first
    | (have := HA ⟨h1, h2⟩; have := HB' ⟨h1', by omega⟩; omega)
    | (have := HA ⟨h1, h2⟩; have := HC' (by omega); omega)
    | (have := HB ⟨h1, by omega⟩; have := HA' ⟨h1', h2'⟩; omega)
    | (have := HB ⟨h1, by omega⟩; have := HC' (by omega); omega)
    | (have := HC (by omega); have := HA' ⟨h1', h2'⟩; omega)
    | (have := HC (by omega); have := HB' ⟨h1', by omega⟩; omega)
    | (simp only [assoc_f, h1, h2, h1', h2', and_self, ↓reduceIte] at h
       exact nat_mul_add_inj h2 h2' h)
    | (simp only [assoc_f, h1, h2, h1', h2', and_false, ↓reduceIte] at h
       have h' : (c - p) * r + a = (c' - p) * r + a' := by omega
       obtain ⟨e1, e2⟩ := nat_mul_add_inj h1 h1' h'
       exact ⟨e2, by omega⟩)
    | (simp only [assoc_f, h1, h1', false_and, ↓reduceIte] at h
       have h' : (a - r) * (q + 1) + c = (a' - r) * (q + 1) + c' := by omega
       obtain ⟨e1, e2⟩ := nat_mul_add_inj hc hc' h'
       exact ⟨by omega, e2⟩)

/-- Helper: the postcondition of `pupd_couple_associativity`, from the defining property of the
coupling relation. -/
theorem assoc_post (p q r s a c t m : ℕ) (Hpq : p ≤ q + 1) (Hrs : r ≤ s + 1)
    (ha : a < s + 1) (hc : c < q + 1)
    (hF : assoc_f p q r a c = if t < p * r then t else p * r + m) :
    if t < p * r then (c < p ∧ a < r)
    else if m < r * (q + 1 - p) then (c ≥ p ∧ a < r) else a ≥ r := by
  obtain ⟨HA, HB, HC⟩ := assoc_f_regions p q r s a c Hpq Hrs ha hc
  have H1 : p * r ≤ r * (q + 1) := by
    rw [Nat.mul_comm p]; exact Nat.mul_le_mul_left _ Hpq
  have Hsplit := assoc_split p q r Hpq
  by_cases ht : t < p * r
  · simp only [ht, ↓reduceIte] at hF ⊢
    by_cases h1 : a < r
    · by_cases h2 : c < p
      · exact ⟨h2, h1⟩
      · have := HB ⟨h1, by omega⟩; omega
    · have := HC (by omega); omega
  · simp only [ht, ↓reduceIte] at hF ⊢
    by_cases hm : m < r * (q + 1 - p)
    · simp only [hm, ↓reduceIte]
      by_cases h1 : a < r
      · by_cases h2 : c < p
        · have := HA ⟨h1, h2⟩; omega
        · exact ⟨by omega, h1⟩
      · have := HC (by omega); omega
    · simp only [hm, ↓reduceIte]
      by_cases h1 : a < r
      · by_cases h2 : c < p
        · have := HA ⟨h1, h2⟩; omega
        · have := HB ⟨h1, by omega⟩; omega
      · omega

/-- Helper: outside of the degenerate case, `p r < (q + 1) (s + 1)`. -/
theorem assoc_pos (p q r s : ℕ) (Hpq : p ≤ q + 1) (Hrs : r ≤ s + 1)
    (Hneq : ¬ (p = q + 1 ∧ r = s + 1)) : p * r < (q + 1) * (s + 1) := by
  by_cases hp : p = q + 1
  · subst hp
    have hr : r < s + 1 := by omega
    exact Nat.mul_lt_mul_of_pos_left hr (by omega)
  · have hp' : p < q + 1 := by omega
    calc p * r ≤ p * (s + 1) := Nat.mul_le_mul_left _ Hrs
      _ < (q + 1) * (s + 1) := Nat.mul_lt_mul_of_pos_right hp' (by omega)

end helpers

section rules

variable {GF : BundledGFunctors} [foxtrotGS GF]

attribute [local instance] specG_con_prob_lang.specG_con_prob_lang_tapes in
/-- Helper (Rocq infers it by unfolding `nat_spec_tape`). -/
instance nat_spec_tape_timeless (l : Loc) (N : ℕ) (ns : List ℕ) :
    Timeless (l ↪ₛN (N; ns) : IProp GF) := by
  unfold nat_spec_tape spec_tapes_frag
  infer_instance

/-- Helper (Rocq: the common part of `wp_couple_rand_rand_lbl`, `wp_couple_rand_lbl_rand_lbl`
and `wp_couple_rand_lbl_rand_lbl_wrong`): a `prog_coupl` coupling a uniform LHS step with a
uniform step of the RHS thread `j`, along a bijection `ff`. -/
theorem prog_coupl_unif_unif (Zb : ℕ) (ff : Fin (Zb + 1) → Fin (Zb + 1))
    (Hff : Function.Bijective ff) (e1 : expr) (σ1 : state) (l : List expr) (s' : state) (j : ℕ)
    (K : List ectx_item) (ε : ℝ≥0∞)
    (Z : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF)
    (Hprim : prim_step (Λ := con_prob_lang) e1 σ1 =
      dmap (fun n : Fin (Zb + 1) =>
        ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, []) : expr × state × List expr)) (dunifP Zb))
    (Hstep : step' j ((l, s') : CPState) =
      dmap (fun n : Fin (Zb + 1) =>
        ((l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), s') : CPState)) (dunifP Zb))
    (Hj : j < l.length) :
    (∀ n : Fin (Zb + 1), |={∅}=> Z (Val (LitV (LitInt ((n : ℕ) : ℤ)))) σ1 []
        ((l.set j (fill K (Val (LitV (LitInt ((ff n : ℕ) : ℤ))))), s') : CPState) ε) ⊢
      prog_coupl e1 σ1 ((l, s') : CPState) ε Z := by
  let g1 : Fin (Zb + 1) → expr × state × List expr := fun n =>
    (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, [])
  let g2 : Fin (Zb + 1) → full_info_state × CPState := fun n =>
    ([(cfg_to_cfg' ((l, s') : CPState), j),
      (cfg_to_cfg' ((l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), s') : CPState),
        (l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))).length)],
      ((l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), s') : CPState))
  have Hlim : osch_lim_exec (full_info_one_step_stutter_osch j).fi_osch ([], ((l, s') : CPState)) =
      dmap g2 (dunifP Zb) :=
    (full_info_one_step_stutter_osch_lim_exec j _).trans
      ((congrArg (dmap _) Hstep).trans (dmap_comp _ _ _))
  iintro H
  iexists (fun x y => ∃ a, x = g1 a ∧ y = g2 (ff a)), full_info_one_step_stutter_osch j, 0,
    (fun _ => ε), ε
  isplitr
  · ipureintro
    refine ⟨g1 0, ?_⟩
    rw [Hprim, dmap_pos]
    exact ⟨0, rfl, dunifP_pos _ _⟩
  isplitr
  · ipureintro
    exact fun _ => le_rfl
  isplitr
  · ipureintro
    rw [zero_add, Expval_const]
    exact mul_le_of_le_one_right zero_le (pmf_SeriesC _)
  isplitr
  · ipureintro
    rw [Hprim, Hlim]
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
    have hab : a = b := Hff.1 (Fin.ext (fill_lit_nat_inj K h))
    subst hab
    exact ⟨rfl, (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm⟩
  iintro %e2 %σ2 %efs %l' %ρ2 %⟨a, h1, h2⟩
  simp only [g1, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
  iapply H $$ %a

/-- Rocq: `pupd_couple_associativity`. Lemma for the associativity of probabilistic choice:
two presamplings on the tapes `α` (bound `s`) and `β` (bound `q`) are coupled with two `rand`s
on the RHS (bounds `(q+1)(s+1) - 1` and `(q+1)(s+1) - p r - 1`). -/
theorem pupd_couple_associativity {p q r s x y : ℕ} (α β : Loc) (ns ns' : List ℕ) (j : ℕ)
    (K : List ectx_item) (j' : ℕ) (K' : List ectx_item) (E : CoPset) (Hpq : p ≤ q + 1)
    (Hrs : r ≤ s + 1) (hx : x = (q + 1) * (s + 1) - 1) (hy : y = (q + 1) * (s + 1) - p * r - 1) :
    ▷ α ↪N (s; ns) ⊢@{IProp GF} ▷ β ↪N (q; ns') -∗
      j ⤇ fill K (Rand (Val (LitV (LitInt (x : ℤ)))) (Val (LitV LitUnit))) -∗
      j' ⤇ fill K' (Rand (Val (LitV (LitInt (y : ℤ)))) (Val (LitV LitUnit))) -∗
      pupd E E iprop(∃ resl resl' resr resr' : ℕ,
        ⌜resl ≤ s⌝ ∗ ⌜resl' ≤ q⌝ ∗ ⌜resr ≤ (q + 1) * (s + 1) - 1⌝ ∗
        ⌜resr' ≤ (q + 1) * (s + 1) - p * r - 1⌝ ∗
        α ↪N (s; ns ++ [resl]) ∗ β ↪N (q; ns' ++ [resl']) ∗
        j ⤇ fill K (Val (LitV (LitInt (resr : ℤ)))) ∗
        j' ⤇ fill K' (Val (LitV (LitInt (resr' : ℤ)))) ∗
        ⌜if resr < p * r then (resl' < p ∧ resl < r)
          else if resr' < r * (q + 1 - p) then (resl' ≥ p ∧ resl < r) else resl ≥ r⌝) := by
  subst hx hy
  by_cases Hdeg : p = q + 1 ∧ r = s + 1
  · obtain ⟨rfl, rfl⟩ := Hdeg
    iintro Hα Hβ H1 H2
    imod Hα
    imod Hβ
    imod pupd_rand j K _ _ E (Int.toNat_natCast _).symm $$ H1 with ⟨%n1, H1, %Hn1⟩
    imod pupd_rand j' K' _ _ E (Int.toNat_natCast _).symm $$ H2 with ⟨%n2, H2, %Hn2⟩
    imod pupd_presample s E ns α $$ Hα with ⟨%a, Hα, %Ha⟩
    imod pupd_presample q E ns' β $$ Hβ with ⟨%c, Hβ, %Hc⟩
    imodintro
    iexists a, c, n1, n2
    have Hpos : 0 < (q + 1) * (s + 1) := Nat.mul_pos (by omega) (by omega)
    isplitr
    · ipureintro; exact Ha
    isplitr
    · ipureintro; exact Hc
    isplitr
    · ipureintro; exact Hn1
    isplitr
    · ipureintro; exact Hn2
    iframe Hα Hβ H1 H2
    ipureintro
    have : n1 < (q + 1) * (s + 1) := by omega
    simp only [this, ↓reduceIte]
    omega
  have HP := assoc_pos p q r s Hpq Hrs Hdeg
  -- Rocq: `f'` and `f`
  have hX : (q + 1) * (s + 1) - 1 + 1 = (q + 1) * (s + 1) := by omega
  let F : Fin (s + 1) × Fin (q + 1) → Fin ((q + 1) * (s + 1) - 1 + 1) := fun ac =>
    ⟨assoc_f p q r ac.1 ac.2, hX ▸ assoc_f_lt p q r s _ _ Hpq Hrs ac.1.2 ac.2.2⟩
  have HFinj : Function.Injective F := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    obtain ⟨h1, h2⟩ := assoc_f_inj p q r s _ _ _ _ Hpq Hrs a.2 c.2 a'.2 c'.2 (congrArg Fin.val h)
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have HF : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨HFinj, ?_⟩
    simp only [Fintype.card_prod, Fintype.card_fin, hX, Nat.mul_comm]
  have Hdecomp := dunifP_decompose s q _ F HF (by rw [Nat.mul_comm])
  -- Rocq: `f_frag`
  let gfrag : ℕ → ℕ := fun n => p * r + n
  have Hginj : Function.Injective gfrag := fun a b h => by simp only [gfrag] at h; omega
  have Hgbound : ∀ n, n < (q + 1) * (s + 1) - p * r - 1 + 1 →
      gfrag n < (q + 1) * (s + 1) - 1 + 1 := fun n hn => by simp only [gfrag]; omega
  have Hfrag := dunif_fragmented _ _ gfrag Hginj Hgbound (by omega)
  unfold pupd pupd_def
  simp only [foxtrotGS_state_interp_eq, foxtrotGS_spec_interp_eq]
  iintro Hα Hβ H1 H2 %σ %⟨l, s'⟩ %εnow ⟨⟨Hh, Ht⟩, Hs, Hε⟩
  imod Hα
  imod Hβ
  iunfold nat_tape at Hα Hβ
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  icases Hβ with ⟨%fs', %Hfs', Hβ⟩
  unfold tapes_auth
  icombine Ht Hα gives %H
  icombine Ht Hβ gives %H'
  rw [ext_get?_eq] at H H'
  ihave %Hne := ghost_map_elem_ne _ _ _ _ _ _ $$ Hα Hβ
  ihave %Hsome := spec_auth_prog_agree l s' j _ $$ Hs H1
  ihave %Hsome' := spec_auth_prog_agree l s' j' _ $$ Hs H2
  ihave %Hjne := spec_prog_frag_ne j j' _ _ $$ H1 H2
  have Hjl : j < l.length := (List.getElem?_eq_some_iff.1 Hsome).1
  have Hjl' : j' < l.length := (List.getElem?_eq_some_iff.1 Hsome').1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  let X := (q + 1) * (s + 1) - 1
  let Y := (q + 1) * (s + 1) - p * r - 1
  let l1 : Fin (X + 1) → List expr := fun n => l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))
  let l2 : Fin (X + 1) → Fin (Y + 1) → List expr := fun n m =>
    (l1 n).set j' (fill K' (Val (LitV (LitInt ((m : ℕ) : ℤ)))))
  let G : Fin (X + 1) → Fin (Y + 1) → full_info_state × CPState := fun n m =>
    ([(cfg_to_cfg' ((l, s') : CPState), j), (cfg_to_cfg' ((l1 n, s') : CPState), j'),
      (cfg_to_cfg' ((l2 n m, s') : CPState), (l2 n m).length)], ((l2 n m, s') : CPState))
  have Hlim : osch_lim_exec (two_step_osch j j').fi_osch ([], ((l, s') : CPState)) =
      dunifP X ≫= fun n => dmap (G n) (dunifP Y) :=
    two_step_osch_lim_exec j j' K K' X Y ((l, s') : CPState) Hjne Hsome Hsome'
  let upd : Fin (s + 1) × Fin (q + 1) → state := fun ac =>
    state_upd_tapes (·.insert β ⟨q, fs' ++ [ac.2]⟩)
      (state_upd_tapes (·.insert α ⟨s, fs ++ [ac.1]⟩) σ)
  have Hμ : (con_prob_lang.state_step σ α ≫= fun σ' => con_prob_lang.state_step σ' β) =
      dunifP X ≫= fun t => dret (upd ((Equiv.ofBijective F HF).symm t)) := by
    rw [state_step_two_unfold σ α β _ _ fs fs' H H' Hne, Hdecomp, ← dbind_assoc]
    refine dbind_ext_right _ _ _ fun a => ?_
    rw [dmap, dmap, ← dbind_assoc]
    simp only [dret_id_left, Equiv.ofBijective_symm_apply_apply]
    rfl
  let S : state → full_info_state × CPState → Prop := fun σ' w =>
    ∃ (t : Fin (X + 1)) (m : Fin (Y + 1)) (ac : Fin (s + 1) × Fin (q + 1)),
      w = G t m ∧ σ' = upd ac ∧
        ((F ac : Fin (X + 1)) : ℕ) = if (t : ℕ) < p * r then (t : ℕ) else p * r + m
  iapply spec_coupl_rec σ ((l, s') : CPState) εnow _
  iexists S, (con_prob_lang.state_step σ α ≫= fun σ' => con_prob_lang.state_step σ' β),
    two_step_osch j j', 0, (fun _ => εnow), εnow
  isplitr
  · ipureintro
    exact state_step_two_sch_erasable σ α β _ _ fs fs' H H' Hne
  isplitr
  · ipureintro
    exact fun _ => le_rfl
  isplitr
  · ipureintro
    rw [zero_add, Expval_const]
    exact mul_le_of_le_one_right zero_le (pmf_SeriesC _)
  isplitr
  · ipureintro
    rw [Hμ, Hfrag, ← dbind_assoc, Hlim]
    refine ARcoupl_dbind' 0 0 0 _ _ _ _ (· = ·) S (add_zero _).symm (fun t t' ht => ?_)
      (ARcoupl_eq _)
    subst ht
    by_cases h : ∃ m : Fin ((q + 1) * (s + 1) - p * r - 1 + 1), gfrag m = (t : ℕ)
    · simp only [h, ↓reduceIte]
      rw [dmap_fold, dmap_comp]
      apply ARcoupl_map
      refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ?_ le_rfl
        (ARcoupl_eq _)
      rintro m m' rfl
      obtain ⟨m0, hm0⟩ := h
      have ht : ¬ (t : ℕ) < p * r := by simp only [gfrag] at hm0; omega
      refine ⟨t, m, _, rfl, rfl, ?_⟩
      rw [Equiv.ofBijective_apply_symm_apply F HF]
      simp only [ht, ↓reduceIte]
      rfl
    · simp only [h, ↓reduceIte, dret_id_left]
      have ht : (t : ℕ) < p * r := by
        by_contra ht
        exact h ⟨⟨(t : ℕ) - p * r, by have := t.2; omega⟩, by simp only [gfrag]; omega⟩
      refine ARcoupl_mono _ _ _ _ _ _ _ _
        (fun b => congrArg (fun μ => μ b) (dbind_const (dunifP Y) _ (dunifP_mass Y)))
        (fun _ => rfl) (fun _ _ h => h) le_rfl ?_
      rw [dmap_fold]
      apply ARcoupl_map
      refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ?_ le_rfl
        (ARcoupl_eq _)
      rintro m m' rfl
      refine ⟨t, m, _, rfl, rfl, ?_⟩
      rw [Equiv.ofBijective_apply_symm_apply F HF]
      simp only [ht, ↓reduceIte]
  isplitr
  · ipureintro
    rintro σx σy ρx ρy L ⟨t1, m1, ac1, h1, rfl, hF1⟩ ⟨t2, m2, ac2, h2, rfl, hF2⟩
    have hL1 : L = (G t1 m1).1 := congrArg Prod.fst h1
    have hL2 : L = (G t2 m2).1 := congrArg Prod.fst h2
    have ha := congrArg (fun L : full_info_state => (L[1]?).map (fun q => q.1.1[j]?))
      (hL1.symm.trans hL2)
    simp only [G, l1, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, List.getElem?_set_self Hjl, Option.some.injEq] at ha
    have htt : t1 = t2 := Fin.ext (fill_lit_nat_inj K ha)
    subst htt
    have hb := congrArg (fun L : full_info_state => (L[2]?).map (fun q => q.1.1[j']?))
      (hL1.symm.trans hL2)
    have Hjl'' : j' < (l1 t1).length := by simpa [l1] using Hjl'
    simp only [G, l2, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.map_some, List.getElem?_set_self Hjl'', Option.some.injEq] at hb
    have hmm : m1 = m2 := Fin.ext (fill_lit_nat_inj K' hb)
    subst hmm
    have hac : ac1 = ac2 := HF.1 (Fin.ext (hF1.trans hF2.symm))
    subst hac
    exact ⟨rfl, (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm⟩
  iintro %σ2 %L %ρ' %⟨t, m, ⟨a, c⟩, h, rfl, hF⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  beta_reduce
  imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((t : ℕ) : ℤ))))) $$ Hs H1
    with ⟨Hs, H1⟩
  imod spec_update_prog (l1 t) s' j' _ (fill K' (Val (LitV (LitInt ((m : ℕ) : ℤ))))) $$ Hs H2
    with ⟨Hs, H2⟩
  imod ghost_map_update (⟨s, fs ++ [a]⟩ : tape) $$ Ht Hα with ⟨Ht, Hα⟩
  imod ghost_map_update (⟨q, fs' ++ [c]⟩ : tape) $$ Ht Hβ with ⟨Ht, Hβ⟩
  rw [ext_insert_eq, ext_insert_eq]
  imodintro
  iapply spec_coupl_ret_pair (upd (a, c)) (l2 t m) s' _ εnow
  imod Hclose
  imodintro
  simp only [upd, state_upd_tapes_heap', state_upd_tapes_tapes]
  iframe Hh Ht Hs Hε
  iexists (a : ℕ), (c : ℕ), (t : ℕ), (m : ℕ)
  isplitr
  · ipureintro; exact Nat.lt_succ_iff.1 a.2
  isplitr
  · ipureintro; exact Nat.lt_succ_iff.1 c.2
  isplitr
  · ipureintro; exact Nat.lt_succ_iff.1 t.2
  isplitr
  · ipureintro; exact Nat.lt_succ_iff.1 m.2
  isplitl [Hα]
  · iunfold nat_tape
    iexists fs ++ [a]
    iframe Hα
    ipureintro
    simp [Hfs]
  isplitl [Hβ]
  · iunfold nat_tape
    iexists fs' ++ [c]
    iframe Hβ
    ipureintro
    simp [Hfs']
  iframe H1 H2
  ipureintro
  exact assoc_post p q r s a c t m Hpq Hrs a.2 c.2 hF

/-- Rocq: `wp_couple_toss`. Coupling `rand #x` with `rand #y`, where `x + 1 = (y + 1) * k`: the
RHS result is the LHS result divided by `k`. -/
theorem wp_couple_toss {x y k : ℕ} (j : ℕ) (K : List ectx_item) {s : Stuckness} {E : CoPset}
    (Hk : 0 < k) (hx : x = (y + 1) * k - 1) :
    {{ j ⤇ fill K (Rand (Val (LitV (LitInt (y : ℤ)))) (Val (LitV LitUnit))) }}
      (Rand (Val (LitV (LitInt (x : ℤ)))) (Val (LitV LitUnit))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ));
      (j ⤇ fill K (Val (LitV (LitInt ((n / k : ℕ) : ℤ)))) : IProp GF) }} := by
  have hk : k - 1 + 1 = k := by omega
  have hx' : x = (y + 1) * (k - 1 + 1) - 1 := by rw [hk]; exact hx
  have hX : x + 1 = (y + 1) * k := by
    have : 0 < (y + 1) * k := Nat.mul_pos (by omega) Hk
    omega
  -- Rocq: `f'` and `f`
  have HFlt : ∀ (n : Fin (y + 1)) (m : Fin (k - 1 + 1)), (n : ℕ) * k + m < x + 1 := by
    intro n m
    rw [hX]
    have h1 : (n : ℕ) * k + m < (n + 1) * k := by
      have := m.2; rw [add_mul, one_mul]; omega
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ n.2)
  let F : Fin (y + 1) × Fin (k - 1 + 1) → Fin (x + 1) := fun p =>
    ⟨(p.1 : ℕ) * k + p.2, HFlt p.1 p.2⟩
  have HFinj : Function.Injective F := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    obtain ⟨h1, h2⟩ := nat_mul_add_inj (k := k) (by have := b.2; omega) (by have := d.2; omega)
      (congrArg Fin.val h)
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have HF : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨HFinj, ?_⟩
    simp only [Fintype.card_prod, Fintype.card_fin, hk, hX]
  have Hdecomp := dunifP_decompose y (k - 1) x F HF hx'
  iintro %Φ Hr HΦ
  iapply wp_lift_step_prog_couple rfl
  simp only [foxtrotGS_spec_interp_eq]
  iintro %σ1 %⟨l, s'⟩ %ε ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree l s' j _ $$ Hs Hr
  have Hj : j < l.length := (List.getElem?_eq_some_iff.1 Hsome).1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  let l1 : Fin (y + 1) → List expr := fun n => l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))
  let G : Fin (y + 1) → Fin (k - 1 + 1) → full_info_state × CPState := fun n m =>
    ([(cfg_to_cfg' ((l, s') : CPState), j), (cfg_to_cfg' ((l1 n, s') : CPState), (m : ℕ) + l.length)],
      ((l1 n, s') : CPState))
  let g1 : Fin (x + 1) → expr × state × List expr := fun n =>
    (Val (LitV (LitInt ((n : ℕ) : ℤ))), σ1, [])
  have Hlim : osch_lim_exec (toss_osch j l.length k).fi_osch ([], ((l, s') : CPState)) =
      dunifP y ≫= fun n => dmap (G n) (dunifP (k - 1)) :=
    toss_osch_lim_exec j k K y ((l, s') : CPState) Hsome
  iexists (fun a b => ∃ n m, a = g1 (F (n, m)) ∧ b = G n m), toss_osch j l.length k, 0,
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
      Option.map_some, List.getElem?_set_self Hj, Option.some.injEq] at ha
    have hnn : n = n' := Fin.ext (fill_lit_nat_inj K ha)
    subst hnn
    have hb := congrArg (fun L : full_info_state => (L[1]?).map Prod.snd) (hL1.symm.trans hL2)
    simp only [G, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
      Option.some.injEq, Nat.add_right_cancel_iff] at hb
    have hmm : m = m' := Fin.ext hb
    subst hmm
    exact ⟨rfl, (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm⟩
  iintro %e2 %σ2 %efs %L %ρ2 %⟨n, m, h1, h2⟩
  simp only [g1, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
  beta_reduce
  imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))) $$ Hs Hr
    with ⟨Hs, Hr⟩
  imodintro
  inext
  imod Hclose
  imodintro
  iframe Hσ Hs Hε
  have hdiv : ((F (n, m) : Fin (x + 1)) : ℕ) / k = n :=
    mul_add_div_of_lt (by have := m.2; omega)
  isplitl
  · iapply wp_value'
    iapply HΦ $$ %((F (n, m) : Fin (x + 1)) : ℕ)
    rw [hdiv]
    iexact Hr
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `pupd_couple_tape_rand`. Exact coupling of a presampling on the tape `α` with a
`rand` on the RHS, along a bijection `f`. -/
theorem pupd_couple_tape_rand (N : ℕ) (f : ℕ → ℕ) (Hbij : Function.Bijective f)
    (K : List ectx_item) (E : CoPset) (α : Loc) (z : ℤ) (ns : List ℕ) (j : ℕ)
    (hN : N = z.toNat) (Hdom : ∀ n : ℕ, n < N + 1 → f n < N + 1) :
    ▷ α ↪N (N; ns) ⊢@{IProp GF}
      j ⤇ fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) -∗
      pupd E E iprop(∃ n : ℕ, α ↪N (N; ns ++ [n]) ∗
        j ⤇ fill K (Val (LitV (LitInt ((f n : ℕ) : ℤ)))) ∗ ⌜n ≤ N⌝) := by
  subst hN
  -- Rocq: `restr_bij_fin`
  let ff : Fin (z.toNat + 1) → Fin (z.toNat + 1) := fun a => ⟨f a, Hdom a a.2⟩
  have Hff_inj : Function.Injective ff := fun a b h => Fin.ext (Hbij.1 (congrArg Fin.val h))
  have Hff : Function.Bijective ff := Finite.injective_iff_bijective.1 Hff_inj
  unfold pupd pupd_def
  simp only [foxtrotGS_state_interp_eq, foxtrotGS_spec_interp_eq]
  iintro Hα Hr %σ %⟨l, s'⟩ %εnow ⟨⟨Hh, Ht⟩, Hs, Hε⟩
  imod Hα
  iunfold nat_tape at Hα
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  unfold tapes_auth
  icombine Ht Hα gives %H
  rw [ext_get?_eq] at H
  ihave %Hlookup := spec_auth_prog_agree l s' j _ $$ Hs Hr
  have Hj : j < l.length := (List.getElem?_eq_some_iff.1 Hlookup).1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  let upd : Fin (z.toNat + 1) → state := fun n =>
    state_upd_tapes (·.insert α ⟨z.toNat, fs ++ [n]⟩) σ
  let g : Fin (z.toNat + 1) → full_info_state × CPState := fun n =>
    ([(cfg_to_cfg' ((l, s') : CPState), j),
      (cfg_to_cfg' ((l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), s') : CPState),
        (l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))).length)],
      ((l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), s') : CPState))
  have Hlim : osch_lim_exec (full_info_one_step_stutter_osch j).fi_osch ([], ((l, s') : CPState)) =
      dmap g (dunifP z.toNat) :=
    (full_info_one_step_stutter_osch_lim_exec j _).trans
      ((congrArg (dmap _) (step'_fill_rand j ((l, s') : CPState) K z Hlookup)).trans
        (dmap_comp _ _ _))
  let S : state → full_info_state × CPState → Prop := fun σ' y =>
    ∃ a : Fin (z.toNat + 1), σ' = upd a ∧ y = g (ff a)
  iapply spec_coupl_rec σ ((l, s') : CPState) εnow _
  iexists S, con_prob_lang.state_step σ α, full_info_one_step_stutter_osch j, 0,
    (fun _ => εnow), εnow
  isplitr
  · ipureintro
    exact state_step_sch_erasable σ α _ H
  isplitr
  · ipureintro
    exact fun _ => le_rfl
  isplitr
  · ipureintro
    rw [zero_add, Expval_const]
    exact mul_le_of_le_one_right zero_le (pmf_SeriesC _)
  isplitr
  · ipureintro
    rw [state_step_unfold σ α z.toNat fs H, Hlim]
    apply ARcoupl_map
    exact ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      (fun a b h => ⟨a, rfl, by rw [h]⟩) le_rfl (ARcoupl_dunif _ ff Hff)
  isplitr
  · ipureintro
    rintro σx σy ρx ρy L ⟨a, rfl, h1⟩ ⟨b, rfl, h2⟩
    have hL1 : L = (g (ff a)).1 := congrArg Prod.fst h1
    have hL2 : L = (g (ff b)).1 := congrArg Prod.fst h2
    have h := congrArg (fun L : full_info_state => (L[1]?).map (fun q => q.1.1[j]?))
      (hL1.symm.trans hL2)
    simp only [g, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
      List.getElem?_set_self Hj, Option.some.injEq] at h
    have hab : a = b := Hff_inj (Fin.ext (fill_lit_nat_inj K h))
    subst hab
    exact ⟨rfl, (congrArg Prod.snd h1).trans (congrArg Prod.snd h2).symm⟩
  iintro %σ2 %L %ρ' %⟨a, rfl, h⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  beta_reduce
  imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((ff a : ℕ) : ℤ))))) $$ Hs Hr
    with ⟨Hs, Hr⟩
  imod ghost_map_update (⟨z.toNat, fs ++ [a]⟩ : tape) $$ Ht Hα with ⟨Ht, Hα⟩
  rw [ext_insert_eq]
  imodintro
  iapply spec_coupl_ret_pair (upd a) (l.set j (fill K (Val (LitV (LitInt ((ff a : ℕ) : ℤ))))))
    s' _ εnow
  imod Hclose
  imodintro
  simp only [upd, state_upd_tapes_heap', state_upd_tapes_tapes]
  iframe Hh Ht Hs Hε
  iexists (a : ℕ)
  isplitl [Hα]
  · iunfold nat_tape
    iexists fs ++ [a]
    iframe Hα
    ipureintro
    simp [Hfs]
  iframe Hr
  ipureintro
  exact Nat.lt_succ_iff.1 a.2

/-- Rocq: `pupd_couple_two_tapes_rand`. Coupling two presamplings on the tapes `α`, `α'` with
one `rand` on the RHS, along a bijection `f : [0, N] × [0, M] → [0, (N+1)(M+1) - 1]`. -/
theorem pupd_couple_two_tapes_rand (N M : ℕ) (f : ℕ → ℕ → ℕ) (K : List ectx_item) (E : CoPset)
    (α α' : Loc) (z z' x : ℤ) (ns ms : List ℕ) (j : ℕ) (hN : N = z.toNat) (hM : M = z'.toNat)
    (hx : x = (((N + 1) * (M + 1) - 1 : ℕ) : ℤ))
    (Hcond1 : ∀ n m, n < N + 1 → m < M + 1 → f n m < (N + 1) * (M + 1))
    (Hcond2 : ∀ n n' m m', n < N + 1 → n' < N + 1 → m < M + 1 → m' < M + 1 →
      f n m = f n' m' → n = n' ∧ m = m')
    (Hcond3 : ∀ x, x < (N + 1) * (M + 1) → ∃ n m, n < N + 1 ∧ m < M + 1 ∧ f n m = x) :
    ▷ α ↪N (N; ns) ⊢@{IProp GF} ▷ α' ↪N (M; ms) -∗
      j ⤇ fill K (Rand (Val (LitV (LitInt x))) (Val (LitV LitUnit))) -∗
      pupd E E iprop(∃ n m : ℕ, α ↪N (N; ns ++ [n]) ∗ α' ↪N (M; ms ++ [m]) ∗
        j ⤇ fill K (Val (LitV (LitInt ((f n m : ℕ) : ℤ)))) ∗ ⌜n ≤ N⌝ ∗ ⌜m ≤ M⌝) := by
  subst hN hM hx
  have hX : (z.toNat + 1) * (z'.toNat + 1) - 1 + 1 = (z.toNat + 1) * (z'.toNat + 1) := by
    have : 0 < (z.toNat + 1) * (z'.toNat + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  -- Rocq: the function `f'` specialised to `fin`
  let F : Fin (z.toNat + 1) × Fin (z'.toNat + 1) →
      Fin ((z.toNat + 1) * (z'.toNat + 1) - 1 + 1) := fun p =>
    ⟨f p.1 p.2, hX ▸ Hcond1 _ _ p.1.2 p.2.2⟩
  have HF : Function.Bijective F := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      obtain ⟨h1, h2⟩ := Hcond2 _ _ _ _ a.2 a'.2 b.2 b'.2 (congrArg Fin.val h)
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · rintro ⟨y, hy⟩
      obtain ⟨n, m, hn, hm, rfl⟩ := Hcond3 y (hX ▸ hy)
      exact ⟨(⟨n, hn⟩, ⟨m, hm⟩), rfl⟩
  have Hdecomp := dunifP_decompose z.toNat z'.toNat _ F HF rfl
  unfold pupd pupd_def
  simp only [foxtrotGS_state_interp_eq, foxtrotGS_spec_interp_eq]
  iintro Hα Hα' Hr %σ %⟨l, s'⟩ %εnow ⟨⟨Hh, Ht⟩, Hs, Hε⟩
  imod Hα
  imod Hα'
  iunfold nat_tape at Hα Hα'
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  icases Hα' with ⟨%fs', %Hfs', Hα'⟩
  unfold tapes_auth
  icombine Ht Hα gives %H
  icombine Ht Hα' gives %H'
  rw [ext_get?_eq] at H H'
  ihave %Hne := ghost_map_elem_ne _ _ _ _ _ _ $$ Hα Hα'
  ihave %Hlookup := spec_auth_prog_agree l s' j _ $$ Hs Hr
  have Hj : j < l.length := (List.getElem?_eq_some_iff.1 Hlookup).1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  let upd : Fin (z.toNat + 1) → Fin (z'.toNat + 1) → state := fun n m =>
    state_upd_tapes (·.insert α' ⟨z'.toNat, fs' ++ [m]⟩)
      (state_upd_tapes (·.insert α ⟨z.toNat, fs ++ [n]⟩) σ)
  let g : Fin ((z.toNat + 1) * (z'.toNat + 1) - 1 + 1) → full_info_state × CPState := fun n =>
    ([(cfg_to_cfg' ((l, s') : CPState), j),
      (cfg_to_cfg' ((l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), s') : CPState),
        (l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ)))))).length)],
      ((l.set j (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))), s') : CPState))
  have Hlim : osch_lim_exec (full_info_one_step_stutter_osch j).fi_osch ([], ((l, s') : CPState)) =
      dmap g (dunifP ((z.toNat + 1) * (z'.toNat + 1) - 1)) :=
    (full_info_one_step_stutter_osch_lim_exec j _).trans
      ((congrArg (dmap _) (step'_fill_rand_nat j ((l, s') : CPState) K _ Hlookup)).trans
        (dmap_comp _ _ _))
  let S : state → full_info_state × CPState → Prop := fun σ' y =>
    ∃ n m, σ' = upd n m ∧ y = g (F (n, m))
  iapply spec_coupl_rec σ ((l, s') : CPState) εnow _
  iexists S, (con_prob_lang.state_step σ α ≫= fun σ' => con_prob_lang.state_step σ' α'),
    full_info_one_step_stutter_osch j, 0, (fun _ => εnow), εnow
  isplitr
  · ipureintro
    exact state_step_two_sch_erasable σ α α' _ _ fs fs' H H' Hne
  isplitr
  · ipureintro
    exact fun _ => le_rfl
  isplitr
  · ipureintro
    rw [zero_add, Expval_const]
    exact mul_le_of_le_one_right zero_le (pmf_SeriesC _)
  isplitr
  · ipureintro
    rw [state_step_two_unfold σ α α' _ _ fs fs' H H' Hne, Hlim, Hdecomp, dmap_dbind]
    refine ARcoupl_dbind' 0 0 0 _ _ _ _ (· = ·) _ (add_zero _).symm (fun n n' hn => ?_)
      (ARcoupl_eq _)
    subst hn
    rw [dmap_comp]
    apply ARcoupl_map
    exact ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      (fun m m' hm => ⟨n, m, rfl, by rw [hm]; rfl⟩) le_rfl (ARcoupl_eq _)
  isplitr
  · ipureintro
    rintro σx σy ρx ρy L ⟨n, m, rfl, h1⟩ ⟨n', m', rfl, h2⟩
    have hL1 : L = (g (F (n, m))).1 := congrArg Prod.fst h1
    have hL2 : L = (g (F (n', m'))).1 := congrArg Prod.fst h2
    have h := congrArg (fun L : full_info_state => (L[1]?).map (fun q => q.1.1[j]?))
      (hL1.symm.trans hL2)
    simp only [g, cfg_to_cfg', List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
      List.getElem?_set_self Hj, Option.some.injEq] at h
    have hnm := HF.1 (Fin.ext (fill_lit_nat_inj K h))
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnm
    exact ⟨rfl, (congrArg Prod.snd h1).trans (congrArg Prod.snd h2).symm⟩
  iintro %σ2 %L %ρ' %⟨n, m, rfl, h⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  beta_reduce
  imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((f n m : ℕ) : ℤ))))) $$ Hs Hr
    with ⟨Hs, Hr⟩
  imod ghost_map_update (⟨z.toNat, fs ++ [n]⟩ : tape) $$ Ht Hα with ⟨Ht, Hα⟩
  imod ghost_map_update (⟨z'.toNat, fs' ++ [m]⟩ : tape) $$ Ht Hα' with ⟨Ht, Hα'⟩
  rw [ext_insert_eq, ext_insert_eq]
  imodintro
  iapply spec_coupl_ret_pair (upd n m)
    (l.set j (fill K (Val (LitV (LitInt ((f n m : ℕ) : ℤ)))))) s' _ εnow
  imod Hclose
  imodintro
  simp only [upd, state_upd_tapes_heap', state_upd_tapes_tapes]
  iframe Hh Ht Hs Hε
  iexists (n : ℕ), (m : ℕ)
  isplitl [Hα]
  · iunfold nat_tape
    iexists fs ++ [n]
    iframe Hα
    ipureintro
    simp [Hfs]
  isplitl [Hα']
  · iunfold nat_tape
    iexists fs' ++ [m]
    iframe Hα'
    ipureintro
    simp [Hfs']
  iframe Hr
  isplitr
  · ipureintro
    exact Nat.lt_succ_iff.1 n.2
  · ipureintro
    exact Nat.lt_succ_iff.1 m.2

/-- Rocq: `wp_couple_rand_rand_lbl`. Coupling `rand #z` with `rand(#lbl:α) #z` on an empty spec
tape, along a bijection `f`. -/
theorem wp_couple_rand_rand_lbl (N : ℕ) (f : ℕ → ℕ) (Hbij : Function.Bijective f) (z : ℤ)
    (K : List ectx_item) {s : Stuckness} {E : CoPset} (α : Loc) (j : ℕ) (hN : N = z.toNat)
    (Hdom : ∀ n : ℕ, n < N + 1 → f n < N + 1) :
    {{ α ↪ₛN (N; []) ∗ j ⤇ fill K (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) }}
      (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ));
      (iprop(α ↪ₛN (N; []) ∗ j ⤇ fill K (Val (LitV (LitInt ((f n : ℕ) : ℤ)))) ∗ ⌜n ≤ N⌝) :
        IProp GF) }} := by
  subst hN
  -- Rocq: `restr_bij_fin`
  let ff : Fin (z.toNat + 1) → Fin (z.toNat + 1) := fun a => ⟨f a, Hdom a a.2⟩
  have Hff_inj : Function.Injective ff := fun a b h => Fin.ext (Hbij.1 (congrArg Fin.val h))
  have Hff : Function.Bijective ff := Finite.injective_iff_bijective.1 Hff_inj
  iintro %Ψ ⟨Hα, Hr⟩ HΨ
  iapply wp_lift_step_prog_couple rfl
  simp only [foxtrotGS_spec_interp_eq]
  iintro %σ1 %⟨l, s'⟩ %ε ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree l s' j _ $$ Hs Hr
  ihave Hα := spec_tapeN_to_empty α z.toNat $$ Hα
  ihave %Hlookup := spec_auth_lookup_tape l s' α _ _ $$ Hs Hα
  have Hj : j < l.length := (List.getElem?_eq_some_iff.1 Hsome).1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply prog_coupl_unif_unif z.toNat ff Hff _ σ1 l s' j K ε _ (prim_step_rand z σ1)
    (step'_fill_unif j ((l, s') : CPState) K _ z.toNat Hsome
      (head_step_rand_lbl_empty z α s' Hlookup)) Hj
  iintro %a
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
    isplitl [Hα]
    · iapply empty_to_spec_tapeN $$ Hα
    iframe Hr
    ipureintro
    exact Nat.lt_succ_iff.1 a.2
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_couple_rand_lbl_rand_lbl`. Coupling `rand(#lbl:α) #z` with `rand(#lbl:α') #z` on
empty tapes, along a bijection `f`. -/
theorem wp_couple_rand_lbl_rand_lbl (N : ℕ) (f : ℕ → ℕ) (Hbij : Function.Bijective f) (z : ℤ)
    (K : List ectx_item) {s : Stuckness} {E : CoPset} (α α' : Loc) (j : ℕ) (hN : N = z.toNat)
    (Hdom : ∀ n : ℕ, n < N + 1 → f n < N + 1) :
    {{ ▷ α ↪N (N; []) ∗ ▷ α' ↪ₛN (N; []) ∗
        j ⤇ fill K (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α')))) }}
      (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ));
      (iprop(α ↪N (N; []) ∗ α' ↪ₛN (N; []) ∗
        j ⤇ fill K (Val (LitV (LitInt ((f n : ℕ) : ℤ)))) ∗ ⌜n ≤ N⌝) : IProp GF) }} := by
  subst hN
  -- Rocq: `restr_bij_fin`
  let ff : Fin (z.toNat + 1) → Fin (z.toNat + 1) := fun a => ⟨f a, Hdom a a.2⟩
  have Hff_inj : Function.Injective ff := fun a b h => Fin.ext (Hbij.1 (congrArg Fin.val h))
  have Hff : Function.Bijective ff := Finite.injective_iff_bijective.1 Hff_inj
  iintro %Ψ ⟨>Htape, >Htape', Hr⟩ HΨ
  iapply wp_lift_step_prog_couple rfl
  simp only [foxtrotGS_state_interp_eq, foxtrotGS_spec_interp_eq]
  iintro %σ1 %⟨l, s'⟩ %ε ⟨⟨Hh, Ht⟩, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree l s' j _ $$ Hs Hr
  ihave Htape' := spec_tapeN_to_empty α' z.toNat $$ Htape'
  ihave %Hsome' := spec_auth_lookup_tape l s' α' _ _ $$ Hs Htape'
  ihave Htape := tapeN_to_empty α z.toNat $$ Htape
  unfold tapes_auth
  icombine Ht Htape gives %Hsome''
  rw [ext_get?_eq] at Hsome''
  have Hj : j < l.length := (List.getElem?_eq_some_iff.1 Hsome).1
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply prog_coupl_unif_unif z.toNat ff Hff _ σ1 l s' j K ε _
    (prim_step_rand_lbl z α σ1 (head_step_rand_lbl_empty z α σ1 Hsome''))
    (step'_fill_unif j ((l, s') : CPState) K _ z.toNat Hsome
      (head_step_rand_lbl_empty z α' s' Hsome')) Hj
  iintro %a
  imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((ff a : ℕ) : ℤ))))) $$ Hs Hr
    with ⟨Hs, Hr⟩
  imodintro
  inext
  imod Hclose
  imodintro
  iframe Hh Ht Hs Hε
  isplitl
  · iapply wp_value'
    iapply HΨ $$ %(a : ℕ)
    isplitl [Htape]
    · iapply empty_to_tapeN $$ Htape
    isplitl [Htape']
    · iapply empty_to_spec_tapeN $$ Htape'
    iframe Hr
    ipureintro
    exact Nat.lt_succ_iff.1 a.2
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_couple_rand_lbl_rand_lbl_wrong`. Coupling `rand(#lbl:α) #z` with
`rand(#lbl:α') #z` on tapes of a wrong bound `M ≠ N`, along a bijection `f`. -/
theorem wp_couple_rand_lbl_rand_lbl_wrong (N M : ℕ) (f : ℕ → ℕ) (Hbij : Function.Bijective f)
    (z : ℤ) (K : List ectx_item) {s : Stuckness} {E : CoPset} (α α' : Loc) (xs ys : List ℕ)
    (j : ℕ) (hN : N = z.toNat) (Hneq : N ≠ M) (Hdom : ∀ n : ℕ, n < N + 1 → f n < N + 1) :
    {{ ▷ α ↪N (M; xs) ∗ ▷ α' ↪ₛN (M; ys) ∗
        j ⤇ fill K (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α')))) }}
      (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ));
      (iprop(α ↪N (M; xs) ∗ α' ↪ₛN (M; ys) ∗
        j ⤇ fill K (Val (LitV (LitInt ((f n : ℕ) : ℤ)))) ∗ ⌜n ≤ N⌝) : IProp GF) }} := by
  subst hN
  -- Rocq: `restr_bij_fin`
  let ff : Fin (z.toNat + 1) → Fin (z.toNat + 1) := fun a => ⟨f a, Hdom a a.2⟩
  have Hff_inj : Function.Injective ff := fun a b h => Fin.ext (Hbij.1 (congrArg Fin.val h))
  have Hff : Function.Bijective ff := Finite.injective_iff_bijective.1 Hff_inj
  iintro %Ψ ⟨>Htape, >Htape', Hr⟩ HΨ
  iapply wp_lift_step_prog_couple rfl
  simp only [foxtrotGS_state_interp_eq, foxtrotGS_spec_interp_eq]
  iintro %σ1 %⟨l, s'⟩ %ε ⟨⟨Hh, Ht⟩, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree l s' j _ $$ Hs Hr
  iunfold nat_tape at Htape
  icases Htape with ⟨%fs, %Hfs, Hα⟩
  iunfold nat_spec_tape at Htape'
  icases Htape' with ⟨%fsₛ, %Hfsₛ, Hαs⟩
  unfold tapes_auth
  icombine Ht Hα gives %Hsome'
  rw [ext_get?_eq] at Hsome'
  ihave %Hsome'' := spec_auth_lookup_tape l s' α' _ _ $$ Hs Hαs
  have Hj : j < l.length := (List.getElem?_eq_some_iff.1 Hsome).1
  have HM : M ≠ z.toNat := fun h => Hneq h.symm
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply prog_coupl_unif_unif z.toNat ff Hff _ σ1 l s' j K ε _
    (prim_step_rand_lbl z α σ1 (head_step_rand_lbl_wrong z α σ1 M fs Hsome' HM))
    (step'_fill_unif j ((l, s') : CPState) K _ z.toNat Hsome
      (head_step_rand_lbl_wrong z α' s' M fsₛ Hsome'' HM)) Hj
  iintro %a
  imod spec_update_prog l s' j _ (fill K (Val (LitV (LitInt ((ff a : ℕ) : ℤ))))) $$ Hs Hr
    with ⟨Hs, Hr⟩
  imodintro
  inext
  imod Hclose
  imodintro
  iframe Hh Ht Hs Hε
  isplitl
  · iapply wp_value'
    iapply HΨ $$ %(a : ℕ)
    isplitl [Hα]
    · iunfold nat_tape
      iexists fs
      iframe Hα
      ipureintro
      exact Hfs
    isplitl [Hαs]
    · iunfold nat_spec_tape
      iexists fsₛ
      iframe Hαs
      ipureintro
      exact Hfsₛ
    iframe Hr
    ipureintro
    exact Nat.lt_succ_iff.1 a.2
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

end rules

end Foxtrot
