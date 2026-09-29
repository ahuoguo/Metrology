module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Countable sums on `ℝ≥0∞`

Ported from clutch/theories/prob/countable_sum.v

The Rocq file develops `SeriesC` (series over a countable type with values in `R`) from
scratch. In the discrete Lean port, all series take values in `ℝ≥0∞`, so `SeriesC f` becomes
Mathlib's `∑' a, f a`, and almost all of `countable_sum.v` is subsumed by Mathlib
(`ENNReal.tsum_*`). Summability side conditions (`ex_seriesC`) disappear because every
`ℝ≥0∞`-valued function is summable (`ENNReal.summable`).

Correspondence for the Rocq lemmas (in particular all those used by `con_prob_lang`, `coneris`
and `foxtrot`). Rocq names not listed here and not defined below are either covered by the
general translation rules (e.g. every `ex_seriesC_*` lemma) or have no downstream use.

General translation rules:
* every `ex_seriesC _` hypothesis/goal disappears (`ENNReal.summable`); so do all
  `ex_seriesC_*` lemmas (`ex_seriesC_finite`, `ex_seriesC_le`, `ex_seriesC_list`,
  `ex_seriesC_ext`, `ex_seriesC_scal_l/r`, `ex_seriesC_plus`, `ex_seriesC_filter_bool_pos`,
  `ex_seriesC_nat_bounded`, `ex_seriesC_singleton(_dependent)`, ...);
* non-negativity hypotheses `0 <= f x` disappear, and `SeriesC_ge_0` is `zero_le`
  (`SeriesC_ge_0'` is also provided below under its Rocq name);
* `is_seriesC f v` is `∑' a, f a = v` (use `HasSum f v` only if genuinely needed);
  `SeriesC_correct` / `SeriesC_correct'` are therefore no-ops (`rfl` / the hypothesis itself);
* `foldr (Rplus ∘ f) 0 l` is `(l.map f).sum`; `sum_n g n` is `∑ i ∈ Finset.range (n + 1), g i`;
* `from_option f 0 o` is `o.elim 0 f`; `gset nat` is `Finset ℕ`;
* `Sup_seq (λ n, _)` is `⨆ n, _`.

Mathlib correspondences:
* `SeriesC_ext` ↦ `tsum_congr`
* `SeriesC_le` / `SeriesC_le'` ↦ `ENNReal.tsum_le_tsum`
* `SeriesC_ge_elem` ↦ `ENNReal.le_tsum`
* `SeriesC_ge_0` ↦ `zero_le`
* `SeriesC_scal_l` / `SeriesC_scal_r` ↦ `ENNReal.tsum_mul_left` / `ENNReal.tsum_mul_right`
* `SeriesC_plus` ↦ `ENNReal.tsum_add`
* `SeriesC_0` / `SeriesC_const0` ↦ `ENNReal.tsum_eq_zero` (`.2` / `.1`)
* `SeriesC_singleton` ↦ `tsum_ite_eq`, `SeriesC_singleton'` ↦ `SeriesC_singleton'` below
* `SeriesC_bool` ↦ `tsum_bool`, `SeriesC_finite_mass` ↦ `tsum_fintype` + `Finset.sum_const`
* `fubini_pos_seriesC` ↦ `ENNReal.tsum_comm`
* `fubini_pos_seriesC_prod_lr` ↦ `ENNReal.tsum_prod`, `..._rl` ↦ `ENNReal.tsum_prod'` + `ENNReal.tsum_comm`
* `SeriesC_nat` / `SeriesC_Series_nat` ↦ (no-op: `∑'` over `ℕ` is already a series)

Lemmas defined below under their Rocq names: `MCT_seriesC` (as `tsum_iSup_of_monotone`),
`SeriesC_singleton'`, `SeriesC_singleton_inj`, `SeriesC_singleton_dependent`,
`SeriesC_split_elem`, `SeriesC_split_pred`, `SeriesC_filter_leq`, `SeriesC_gtz_ex`,
`SeriesC_pos`, `SeriesC_subset`, `SeriesC_list`, `SeriesC_list_1`, `SeriesC_list_2`,
`SeriesC_finite_foldr` (+ `SeriesC_finite_foldr_list`), `SeriesC_Sup_seq_swap`,
`SeriesC_le_inj`, `fin_function_bounded` (+ `ℝ≥0∞` version `fin_function_bounded'`),
`SeriesC_lt` (needs `∑' g ≠ ∞`), `extend_fin_to_R`, `SeriesC_fin_sum`, `SeriesC_nat_bounded`,
`SeriesC_nat_bounded_fin`, `SeriesC_fin2`, `SeriesC_fin_in_set`, `SeriesC_fin_in_set'`,
`SeriesC_fin_not_in_set`, `SeriesC_fin_not_in_set'`, `SeriesC_ge_0'`,
`is_seriesC_filter_union` (stated additively).
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Prob

variable {α β : Type*}

/-- Monotone convergence for countable sums (Rocq: `MCT_seriesC`). -/
theorem tsum_iSup_of_monotone {f : ℕ → α → ℝ≥0∞} (hf : ∀ a, Monotone (fun n => f n a)) :
    ∑' a, ⨆ n, f n a = ⨆ n, ∑' a, f n a := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  congr 1
  funext s
  exact ENNReal.finsetSum_iSup_of_monotone hf

/-- Rocq: `SeriesC_ge_0'` (trivial in `ℝ≥0∞`; kept for name-for-name translation). -/
theorem SeriesC_ge_0' (f : α → ℝ≥0∞) (_ : ∀ x, 0 ≤ f x) : 0 ≤ ∑' a, f a := zero_le

/-- Rocq: `SeriesC_singleton'`. -/
theorem SeriesC_singleton' [DecidableEq α] (a : α) (v : ℝ≥0∞) :
    ∑' a', (if a = a' then v else 0) = v := by
  simp

/-- Rocq: `SeriesC_singleton_inj`. -/
theorem SeriesC_singleton_inj {f : α → β} (hf : Function.Injective f) (b : β) (v : ℝ≥0∞)
    [DecidablePred fun a => f a = b] (h : ∃ a, f a = b) :
    ∑' a, (if f a = b then v else 0) = v := by
  obtain ⟨a0, rfl⟩ := h
  rw [tsum_eq_single a0]
  · simp
  · intro a ha
    simp [hf.ne ha]

/-- Rocq: `SeriesC_list_2` / `SeriesC_finite_mass` specialised to a finset indicator. -/
theorem SeriesC_finset_indicator (s : Finset α) (c : ℝ≥0∞) [DecidablePred (· ∈ s)] :
    ∑' a, (if a ∈ s then c else 0) = s.card * c := by
  rw [tsum_eq_sum (s := s)]
  · rw [Finset.sum_congr rfl (g := fun _ => c) (fun a ha => by simp [ha]), Finset.sum_const,
      nsmul_eq_mul]
  · intro a ha; simp [ha]

/-- Rocq: `SeriesC_split_elem`. -/
theorem SeriesC_split_elem [DecidableEq α] (f : α → ℝ≥0∞) (a0 : α) :
    ∑' a, f a = ∑' a, (if a = a0 then f a else 0) + ∑' a, (if a ≠ a0 then f a else 0) := by
  rw [← ENNReal.tsum_add]
  congr 1; funext a
  by_cases h : a = a0 <;> simp [h]

/-- Rocq: `SeriesC_split_pred`. -/
theorem SeriesC_split_pred (f : α → ℝ≥0∞) (P : α → Bool) :
    ∑' a, f a = ∑' a, (if P a then f a else 0) + ∑' a, (if !P a then f a else 0) := by
  rw [← ENNReal.tsum_add]
  congr 1; funext a
  cases P a <;> simp

/-- Rocq: `SeriesC_filter_leq`. -/
theorem SeriesC_filter_leq (f : α → ℝ≥0∞) (P : α → Prop) [DecidablePred P] :
    ∑' a, (if P a then f a else 0) ≤ ∑' a, f a :=
  ENNReal.tsum_le_tsum fun a => by split_ifs <;> simp

/-- Rocq: `SeriesC_gtz_ex`. -/
theorem SeriesC_gtz_ex (f : α → ℝ≥0∞) (h : 0 < ∑' a, f a) : ∃ a, 0 < f a := by
  by_contra H
  push Not at H
  have : ∑' a, f a = 0 := ENNReal.tsum_eq_zero.2 fun a => nonpos_iff_eq_zero.1 (H a)
  exact absurd h (by simp [this])

/-- Rocq: `SeriesC_pos`. -/
theorem SeriesC_pos (f : α → ℝ≥0∞) (a : α) (h : 0 < f a) : 0 < ∑' a, f a :=
  lt_of_lt_of_le h (ENNReal.le_tsum a)

/-! ## Further lemmas used downstream (Coneris / Foxtrot / con_prob_lang) -/

/-- Rocq: `SeriesC_singleton_dependent`. -/
theorem SeriesC_singleton_dependent [DecidableEq α] (a : α) (v : α → ℝ≥0∞) :
    ∑' n, (if n = a then v n else 0) = v a := by
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [hb]

/-- Rocq: `SeriesC_subset`. -/
theorem SeriesC_subset (g : α → Prop) [DecidablePred g] (f : α → ℝ≥0∞)
    (h : ∀ a, ¬ g a → f a = 0) :
    ∑' a, f a = ∑' a, (if g a then f a else 0) := by
  congr 1; funext a
  by_cases ha : g a <;> simp [ha, h]

/-- Rocq: `SeriesC_list`. Rocq's `foldr (Rplus ∘ f) 0 l` is `(l.map f).sum`. -/
theorem SeriesC_list [DecidableEq α] (l : List α) (f : α → ℝ≥0∞) (hl : l.Nodup) :
    ∑' a, (if a ∈ l then f a else 0) = (l.map f).sum := by
  rw [tsum_eq_sum (s := l.toFinset)]
  · rw [Finset.sum_congr rfl (g := f) (fun a ha => by simp [List.mem_toFinset.1 ha]),
      List.sum_toFinset f hl]
  · intro a ha; simp [List.mem_toFinset.not.1 ha]

/-- Rocq: `SeriesC_list_1`. -/
theorem SeriesC_list_1 [DecidableEq α] (l : List α) (hl : l.Nodup) :
    ∑' a, (if a ∈ l then (1 : ℝ≥0∞) else 0) = l.length := by
  rw [SeriesC_list l (fun _ => 1) hl]; simp

/-- Rocq: `SeriesC_list_2`. -/
theorem SeriesC_list_2 [DecidableEq α] (l : List α) (r : ℝ≥0∞) (hl : l.Nodup) :
    ∑' a, (if a ∈ l then r else 0) = r * l.length := by
  rw [SeriesC_list l (fun _ => r) hl]; simp [mul_comm]

/-- Rocq: `SeriesC_finite_foldr`. Rocq's `foldr (Rplus ∘ f) 0 (enum A)` over a `Finite` type
becomes the `Finset.univ` sum (this is Mathlib's `tsum_fintype`). See also
`SeriesC_finite_foldr_list` for an explicit enumeration. -/
theorem SeriesC_finite_foldr [Fintype α] (f : α → ℝ≥0∞) : ∑' a, f a = ∑ a, f a :=
  tsum_fintype f

/-- Rocq: `SeriesC_finite_foldr` with an explicit duplicate-free enumeration `l`
(the analogue of `enum A`). -/
theorem SeriesC_finite_foldr_list (l : List α) (hl : l.Nodup) (hall : ∀ a, a ∈ l)
    (f : α → ℝ≥0∞) : ∑' a, f a = (l.map f).sum := by
  classical
  rw [← SeriesC_list l f hl]
  simp [hall]

/-- Rocq: `SeriesC_Sup_seq_swap`. The boundedness / summability hypotheses of the Rocq statement
disappear in `ℝ≥0∞`; monotonicity is stated stepwise as in Rocq. -/
theorem SeriesC_Sup_seq_swap (h : ℕ → α → ℝ≥0∞) (hmono : ∀ n a, h n a ≤ h (n + 1) a) :
    ∑' a, ⨆ n, h n a = ⨆ n, ∑' a, h n a :=
  tsum_iSup_of_monotone fun a => monotone_nat_of_le_succ fun n => hmono n a

/-- Rocq: `SeriesC_le_inj`. `from_option f 0 (h a)` is `(h a).elim 0 f`. -/
theorem SeriesC_le_inj (f : β → ℝ≥0∞) (h : α → Option β)
    (hinj : ∀ n1 n2 m, h n1 = some m → h n2 = some m → n1 = n2) :
    ∑' a, (h a).elim 0 f ≤ ∑' b, f b := by
  classical
  have e : ∀ a, (h a).elim 0 f = ∑' b, (if h a = some b then f b else 0) := by
    intro a
    cases ha : h a with
    | none => simp
    | some b0 =>
      rw [tsum_eq_single b0]
      · simp
      · intro b hb; simp [Ne.symm hb]
  simp_rw [e]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun b => ?_
  by_cases hex : ∃ a0, h a0 = some b
  · obtain ⟨a0, ha0⟩ := hex
    rw [tsum_eq_single a0]
    · simp [ha0]
    · intro a ha
      have : h a ≠ some b := fun hab => ha (hinj a a0 b hab ha0)
      simp [this]
  · push Not at hex
    simp [hex]

/-- Rocq: `fin_function_bounded` (real-valued, as in Rocq). -/
theorem fin_function_bounded (N : ℕ) (f : Fin N → ℝ) : ∃ r, ∀ n, f n ≤ r :=
  ⟨∑ n, |f n|, fun n => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun n => |f n|) (fun _ _ => abs_nonneg _) (Finset.mem_univ n))⟩

/-- Rocq: `fin_function_bounded`, `ℝ≥0∞` version: a finite family of finite values has a
finite upper bound. (Without the `≠ ∞` hypothesis the statement is trivial with `r = ∞`.) -/
theorem fin_function_bounded' (N : ℕ) (f : Fin N → ℝ≥0∞) (hf : ∀ n, f n ≠ ∞) :
    ∃ r, r ≠ ∞ ∧ ∀ n, f n ≤ r :=
  ⟨∑ n, f n, ENNReal.sum_ne_top.2 fun n _ => hf n,
    fun n => Finset.single_le_sum (f := f) (fun _ _ => zero_le) (Finset.mem_univ n)⟩

/-- Rocq: `SeriesC_lt`. In `ℝ≥0∞` the strict inequality needs the larger sum to be finite. -/
theorem SeriesC_lt (f g : α → ℝ≥0∞) (hle : ∀ n, f n ≤ g n) (hlt : ∃ m, f m < g m)
    (hg : ∑' a, g a ≠ ∞) : ∑' a, f a < ∑' a, g a := by
  obtain ⟨m, hm⟩ := hlt
  exact ENNReal.tsum_lt_tsum (ne_top_of_le_ne_top hg (ENNReal.tsum_le_tsum hle)) hle hm

/-- Rocq: `extend_fin_to_R`: extend `f : Fin n → ℝ≥0∞` by `0` to all of `ℕ`. -/
def extend_fin_to_R {n : ℕ} (f : Fin n → ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun x => if h : x < n then f ⟨x, h⟩ else 0

/-- Rocq: `SeriesC_fin_sum`. Rocq's `sum_n g n` is `∑ i ∈ Finset.range (n + 1), g i`. -/
theorem SeriesC_fin_sum {n : ℕ} (f : Fin (n + 1) → ℝ≥0∞) :
    ∑' i, f i = ∑ i ∈ Finset.range (n + 1), extend_fin_to_R f i := by
  rw [tsum_fintype, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [extend_fin_to_R, i.isLt]

/-- Rocq: `SeriesC_nat_bounded`. -/
theorem SeriesC_nat_bounded (f : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑' n, (if n ≤ N then f n else 0) = ∑ i ∈ Finset.range (N + 1), f i := by
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp [Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)]
  · intro i hi
    have : ¬ i ≤ N := fun h => hi (Finset.mem_range.2 (Nat.lt_succ_of_le h))
    simp [this]

/-- Rocq: `SeriesC_nat_bounded_fin`. -/
theorem SeriesC_nat_bounded_fin (f : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑' n, (if n ≤ N then f n else 0) = ∑' n : Fin (N + 1), f n := by
  rw [SeriesC_nat_bounded, tsum_fintype, Fin.sum_univ_eq_sum_range (fun i => f i)]

/-- Rocq: `SeriesC_fin2`. -/
theorem SeriesC_fin2 (f : Fin 2 → ℝ≥0∞) : ∑' i, f i = f 0 + f 1 := by
  rw [tsum_fintype, Fin.sum_univ_two]

/-- Rocq: `SeriesC_fin_in_set` (Rocq's `gset nat` is a `Finset ℕ`). -/
theorem SeriesC_fin_in_set (N : ℕ) (ns : Finset ℕ) (hns : ∀ x ∈ ns, x < N + 1) :
    ∑' x : Fin (N + 1), (if (x : ℕ) ∈ ns then (1 : ℝ≥0∞) else 0) = ns.card := by
  rw [tsum_fintype, Fin.sum_univ_eq_sum_range (fun i => if i ∈ ns then (1 : ℝ≥0∞) else 0),
    Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext x
  simp only [Finset.mem_inter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hns x h, h⟩⟩

/-- Rocq: `SeriesC_fin_not_in_set`. -/
theorem SeriesC_fin_not_in_set (N : ℕ) (ns : Finset ℕ) (hns : ∀ x ∈ ns, x < N + 1) :
    ∑' x : Fin (N + 1), (if (x : ℕ) ∉ ns then (1 : ℝ≥0∞) else 0) = (N + 1 : ℝ≥0∞) - ns.card := by
  refine ENNReal.eq_sub_of_add_eq (by simp) ?_
  rw [← SeriesC_fin_in_set N ns hns, ← ENNReal.tsum_add]
  rw [show (fun x : Fin (N + 1) => (if (x : ℕ) ∉ ns then (1 : ℝ≥0∞) else 0) +
      (if (x : ℕ) ∈ ns then 1 else 0)) = fun _ => 1 by
    funext x; by_cases h : (x : ℕ) ∈ ns <;> simp [h]]
  simp

/-- Rocq: `SeriesC_fin_in_set'`. -/
theorem SeriesC_fin_in_set' (N : ℕ) (ns : Finset ℕ) (v : ℝ≥0∞) (hns : ∀ x ∈ ns, x < N + 1) :
    ∑' x : Fin (N + 1), (if (x : ℕ) ∈ ns then v else 0) = v * ns.card := by
  rw [← SeriesC_fin_in_set N ns hns, ← ENNReal.tsum_mul_left]
  congr 1; funext x; split_ifs <;> simp

/-- Rocq: `SeriesC_fin_not_in_set'`. -/
theorem SeriesC_fin_not_in_set' (N : ℕ) (ns : Finset ℕ) (v : ℝ≥0∞) (hns : ∀ x ∈ ns, x < N + 1) :
    ∑' x : Fin (N + 1), (if (x : ℕ) ∉ ns then v else 0) = v * ((N + 1 : ℝ≥0∞) - ns.card) := by
  rw [← SeriesC_fin_not_in_set N ns hns, ← ENNReal.tsum_mul_left]
  congr 1; funext x; split_ifs <;> simp

/-- Rocq: `is_seriesC_filter_union`, stated additively (no subtraction needed in `ℝ≥0∞`). -/
theorem is_seriesC_filter_union (f : α → ℝ≥0∞) (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] :
    ∑' n, (if P n then f n else 0) + ∑' n, (if Q n then f n else 0) =
      ∑' n, (if P n ∨ Q n then f n else 0) + ∑' n, (if P n ∧ Q n then f n else 0) := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  congr 1; funext n
  by_cases hP : P n <;> by_cases hQ : Q n <;> simp [hP, hQ]

end Prob
