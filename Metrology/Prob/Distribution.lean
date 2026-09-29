module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Vector.Basic
public import Metrology.Prob.CountableSum

/-!
# Discrete sub-probability distributions

Ported from clutch/theories/prob/distribution.v

A `Distr α` over a countable type is a function `α → ℝ≥0∞` whose total mass is at most `1`.
Compared with the Rocq development (real-valued pmf):
* `SeriesC μ` becomes `∑' a, μ a`;
* non-negativity (`pmf_pos`) and summability (`ex_seriesC`, `ex_expval`) side conditions
  disappear;
* `μ a > 0` becomes `0 < μ a`;
* `Sup_seq` / `is_sup_seq` become `⨆ n, _`;
* bounded real functions (e.g. the argument of `Expval`) become `α → ℝ≥0∞`;
* the fair coin weight `0.5` / `1/2` is written `2⁻¹`.

Trivial-in-`ℝ≥0∞` Rocq lemmas are still provided under their Rocq names (`pmf_pos`,
`pmf_SeriesC_ge_0`, `Expval_ge_0`, `Expval_ge_0'`, ...) so that downstream ports can translate
name-for-name; generally, any Rocq goal `0 <= _` about `ℝ≥0∞` values is closed by `zero_le`.

The Rocq tactics `inv_distr`, `solve_distr`, `solve_distr_mass` and `inv_dzero` are provided
as Lean tactics of the same names at the end of this file.
Intentionally omitted (trivial or vacuous in the `ℝ≥0∞` setting):
* `distr_dec`: equality of distributions is decidable classically;
* `Proper_dbind`: rewriting under binders (`congr`, `simp_rw`) replaces setoid rewriting;
* `Rinv_0_le`, `pmf_ex_seriesC_mult`, `pmf_ex_seriesC_mult_fn`, `distr_double_swap_ex`,
  `distr_double_swap_lmarg_ex`, `distr_double_swap_rmarg_ex` (and other `*_ex` variants),
  `ex_expval_*`, `ex_distr_lmarg`, `ex_distr_rmarg`, `ex_seriesC_sum_f_R0`: non-negativity and
  summability are automatic in `ℝ≥0∞`;
* `SeriesC_sum_f_R0`: a finite sum commutes with `∑'` via
  `Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)`.

The Laplace distribution (`laplace_f_nat`, `laplace_f`, `laplace_f_nat_pos`,
`ex_seriesC_laplace_f(_nat)`, `laplace'`, `laplace`, `laplace_mass`, `laplace_rat`,
`laplace_rat_pos`, `laplace_rat_mass`) is not ported: it is used only by the
differential-privacy/caliper developments, which are out of scope.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Prob

/-- A discrete sub-probability distribution (Rocq: `distr`). -/
structure Distr (α : Type*) [Countable α] where
  /-- The probability mass function. -/
  pmf : α → ℝ≥0∞
  /-- Total mass is at most one (Rocq: `pmf_SeriesC`). -/
  mass_le_one : ∑' a, pmf a ≤ 1

instance {α : Type*} [Countable α] : CoeFun (Distr α) (fun _ => α → ℝ≥0∞) := ⟨Distr.pmf⟩

variable {α β γ δ : Type*} [Countable α] [Countable β] [Countable γ] [Countable δ]

@[simp] theorem Distr.coe_mk (f : α → ℝ≥0∞) (h : ∑' a, f a ≤ 1) (a : α) :
    (⟨f, h⟩ : Distr α) a = f a := rfl

/-- Rocq: `distr_ext`. -/
@[ext] theorem distr_ext {μ₁ μ₂ : Distr α} (h : ∀ a, μ₁ a = μ₂ a) : μ₁ = μ₂ := by
  cases μ₁; cases μ₂; congr; funext a; exact h a

/-- Rocq: `distr_ext_pmf`. -/
theorem distr_ext_pmf {μ₁ μ₂ : Distr α} (h : μ₁.pmf = μ₂.pmf) : μ₁ = μ₂ :=
  distr_ext fun a => congrFun h a

/-! ## Basic facts -/

section distributions

/-- Rocq: `pmf_SeriesC`. -/
theorem pmf_SeriesC (μ : Distr α) : ∑' a, μ a ≤ 1 := μ.mass_le_one

/-- Rocq: `pmf_le_SeriesC`. -/
theorem pmf_le_SeriesC (μ : Distr α) (a : α) : μ a ≤ ∑' a, μ a := ENNReal.le_tsum a

/-- Rocq: `pmf_le_1`. -/
theorem pmf_le_1 (μ : Distr α) (a : α) : μ a ≤ 1 := (pmf_le_SeriesC μ a).trans μ.mass_le_one

theorem pmf_ne_top (μ : Distr α) (a : α) : μ a ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (pmf_le_1 μ a)

theorem SeriesC_ne_top (μ : Distr α) : ∑' a, μ a ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top μ.mass_le_one

/-- Rocq: `pmf_pos` (the structure field; trivial in `ℝ≥0∞`). Kept as a name so that downstream
ports can translate `pmf_pos` mechanically. -/
theorem pmf_pos (μ : Distr α) (a : α) : 0 ≤ μ a := zero_le

/-- Rocq: `pmf_SeriesC_ge_0` (trivial in `ℝ≥0∞`). -/
theorem pmf_SeriesC_ge_0 (μ : Distr α) : 0 ≤ ∑' a, μ a := zero_le

/-- Rocq: `pmf_1_eq_SeriesC`. -/
theorem pmf_1_eq_SeriesC (μ : Distr α) (a : α) (h : μ a = 1) : μ a = ∑' a, μ a :=
  le_antisymm (pmf_le_SeriesC μ a) (h ▸ μ.mass_le_one)

/-- Rocq: `pmf_plus_neq_SeriesC`. -/
theorem pmf_plus_neq_SeriesC (μ : Distr α) (a a' : α) (h : a ≠ a') :
    μ a + μ a' ≤ ∑' a, μ a := by
  classical
  have := ENNReal.sum_le_tsum (f := μ.pmf) {a, a'}
  rwa [Finset.sum_pair h] at this

/-- Rocq: `pmf_1_supp_eq`. -/
theorem pmf_1_supp_eq (μ : Distr α) (a a' : α) (ha : μ a = 1) (ha' : 0 < μ a') : a = a' := by
  by_contra hne
  have h1 := (pmf_plus_neq_SeriesC μ a a' hne).trans μ.mass_le_one
  rw [ha] at h1
  have : μ a' ≤ 0 := by
    have h2 : 1 + μ a' ≤ 1 + 0 := by simpa using h1
    exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 h2
  exact absurd ha' (not_lt.2 this)

/-- Rocq: `is_finite_Sup_seq_distr`. -/
theorem is_finite_Sup_seq_distr (f : ℕ → Distr α) (a : α) : (⨆ n, f n a) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun n => pmf_le_1 (f n) a)

/-- Rocq: `pmf_eq_0_le`. -/
theorem pmf_eq_0_le (μ : Distr α) (a : α) (h : μ a ≤ 0) : μ a = 0 := nonpos_iff_eq_zero.1 h

/-- Rocq: `pmf_eq_0_not_gt_0`. -/
theorem pmf_eq_0_not_gt_0 (μ : Distr α) (a : α) (h : ¬ 0 < μ a) : μ a = 0 :=
  nonpos_iff_eq_zero.1 (not_lt.1 h)

/-- Rocq: `pmf_mult_eq_0`. -/
theorem pmf_mult_eq_0 (μ : Distr α) (μ' : Distr β) (a : α) (b : β)
    (h : 0 < μ a → μ a * μ' b = 0) : μ a * μ' b = 0 := by
  rcases eq_or_ne (μ a) 0 with h0 | h0
  · simp [h0]
  · exact h (pos_iff_ne_zero.2 h0)

end distributions

/-! ## Sum-swapping equalities for distributions -/

/-- Rocq: `distr_double_swap`. -/
theorem distr_double_swap (f : α → Distr β) (μ : Distr α) :
    ∑' b, ∑' a, μ a * f a b = ∑' a, ∑' b, μ a * f a b := ENNReal.tsum_comm

/-- Rocq: `distr_double_lr`. -/
theorem distr_double_lr (f : α → Distr β) (μ : Distr α) :
    ∑' p : α × β, μ p.1 * f p.1 p.2 = ∑' a, ∑' b, μ a * f a b :=
  ENNReal.tsum_prod (f := fun a b => μ a * f a b)

/-- Rocq: `distr_double_rl`. -/
theorem distr_double_rl (f : α → Distr β) (μ : Distr α) :
    ∑' p : α × β, μ p.1 * f p.1 p.2 = ∑' b, ∑' a, μ a * f a b := by
  rw [ENNReal.tsum_prod (f := fun a b => μ a * f a b), ENNReal.tsum_comm]

/-- Rocq: `distr_double_swap_rmarg`. -/
theorem distr_double_swap_rmarg {β' : Type*} [Countable β'] (f : α → Distr (β × β'))
    (μ : Distr α) (b' : β') :
    ∑' a, ∑' b, μ a * f a (b, b') = ∑' b, ∑' a, μ a * f a (b, b') := ENNReal.tsum_comm

/-- Rocq: `distr_double_swap_lmarg`. -/
theorem distr_double_swap_lmarg {β' : Type*} [Countable β'] (f : α → Distr (β × β'))
    (μ : Distr α) (b : β) :
    ∑' a, ∑' b', μ a * f a (b, b') = ∑' b', ∑' a, μ a * f a (b, b') := ENNReal.tsum_comm

/-! ## Monadic return -/

open Classical in
/-- Rocq: `dret_pmf`. -/
def dret_pmf (a : α) : α → ℝ≥0∞ := fun a' => if a' = a then 1 else 0

/-- Rocq: `dret`. -/
def dret (a : α) : Distr α where
  pmf := dret_pmf a
  mass_le_one := by classical simp [dret_pmf]

section dret

/-- Rocq: `dret_pmf_unfold`. -/
theorem dret_pmf_unfold [DecidableEq α] (a a' : α) :
    dret a a' = if a' = a then 1 else 0 := by
  simp only [dret, dret_pmf, Distr.coe_mk]; congr

/-- Rocq: `dret_1`. -/
theorem dret_1 (a a' : α) : a = a' ↔ dret a a' = 1 := by
  classical
  rw [dret_pmf_unfold]
  constructor
  · rintro rfl; simp
  · intro h; by_contra hne; simp [Ne.symm hne] at h

/-- Rocq: `dret_1_1`. -/
theorem dret_1_1 (a a' : α) (h : a = a') : dret a a' = 1 := (dret_1 a a').1 h

/-- Rocq: `dret_1_2`. -/
theorem dret_1_2 (a a' : α) (h : dret a a' = 1) : a = a' := (dret_1 a a').2 h

/-- Rocq: `dret_0`. -/
theorem dret_0 (a a' : α) (h : a' ≠ a) : dret a a' = 0 := by
  classical rw [dret_pmf_unfold]; simp [h]

/-- Rocq: `dret_pos`. -/
theorem dret_pos (a a' : α) (h : 0 < dret a a') : a' = a := by
  by_contra hne; rw [dret_0 a a' hne] at h; exact lt_irrefl _ h

theorem dret_pos_iff (a a' : α) : 0 < dret a a' ↔ a' = a :=
  ⟨dret_pos a a', fun h => by rw [dret_1_1 _ _ h.symm]; exact one_pos⟩

/-- Rocq: `dret_pmf_map`. -/
theorem dret_pmf_map (f : α → α) (hf : Function.Injective f) (a a' : α) :
    dret (f a) (f a') = dret a a' := by
  classical simp only [dret_pmf_unfold, hf.eq_iff]

/-- Rocq: `pmf_1_eq_dret`. -/
theorem pmf_1_eq_dret (μ : Distr α) (a : α) (h : μ a = 1) : μ = dret a := by
  ext a'
  by_cases hne : a = a'
  · subst hne; rw [h, dret_1_1 a a rfl]
  · rw [dret_0 a a' (Ne.symm hne)]
    by_contra h'
    exact hne (pmf_1_supp_eq μ a a' h (pos_iff_ne_zero.2 h'))

/-- Rocq: `pmf_1_not_eq`. -/
theorem pmf_1_not_eq (μ : Distr α) (a a' : α) (hne : a ≠ a') (h : μ a = 1) : μ a' = 0 := by
  rw [pmf_1_eq_dret μ a h]; exact dret_0 a a' (Ne.symm hne)

/-- Rocq: `dret_mass`. -/
@[simp] theorem dret_mass (a : α) : ∑' a', dret a a' = 1 := by
  classical simp [dret_pmf_unfold]

end dret

/-! ## Monadic bind -/

/-- Rocq: `dbind_pmf`. -/
def dbind_pmf (f : α → Distr β) (μ : Distr α) : β → ℝ≥0∞ :=
  fun b => ∑' a, μ a * f a b

/-- Rocq: `dbind`. -/
def dbind (f : α → Distr β) (μ : Distr α) : Distr β where
  pmf := dbind_pmf f μ
  mass_le_one := by
    simp only [dbind_pmf]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    calc ∑' a, μ a * ∑' b, f a b ≤ ∑' a, μ a * 1 :=
          ENNReal.tsum_le_tsum fun a => mul_le_mul_right (f a).mass_le_one _
      _ ≤ 1 := by simpa using μ.mass_le_one

/-- `μ ≫= f` is `dbind f μ` (Rocq: `m ≫= f`). -/
scoped notation:60 m:61 " ≫= " f:60 => dbind f m

/-- Rocq: `dbind_unfold_pmf`. -/
theorem dbind_unfold_pmf (μ₁ : Distr α) (μ₂ : α → Distr β) (b : β) :
    (μ₁ ≫= μ₂) b = ∑' a, μ₁ a * μ₂ a b := rfl

/-- Rocq: `dbind_pmf_ext`. -/
theorem dbind_pmf_ext (μ₁ μ₂ : Distr α) (f g : α → Distr β) (b₁ b₂ : β)
    (hfg : ∀ a b, f a b = g a b) (hμ : μ₁ = μ₂) (hb : b₁ = b₂) :
    dbind f μ₁ b₁ = dbind g μ₂ b₂ := by
  subst hμ hb; simp only [dbind_unfold_pmf, hfg]

/-- Rocq: `dbind_ext_right`. -/
theorem dbind_ext_right (μ : Distr α) (f g : α → Distr β) (h : ∀ a, f a = g a) :
    dbind f μ = dbind g μ := by
  rw [funext h]

/-- Rocq: `dbind_ext_right_strong`. -/
theorem dbind_ext_right_strong (μ : Distr α) (f g : α → Distr β)
    (h : ∀ a, 0 < μ a → f a = g a) : dbind f μ = dbind g μ := by
  ext b
  simp only [dbind_unfold_pmf]
  congr 1; funext a
  rcases eq_or_ne (μ a) 0 with h0 | h0
  · simp [h0]
  · rw [h a (pos_iff_ne_zero.2 h0)]

/-- Rocq: `dbind_ext_right'`. -/
theorem dbind_ext_right' (μ₁ μ₂ : Distr α) (f g : α → Distr β) (h : ∀ a, f a = g a)
    (hμ : μ₁ = μ₂) : dbind f μ₁ = dbind g μ₂ := by
  subst hμ; exact dbind_ext_right _ _ _ h

/-- Rocq: `dbind_const`. -/
theorem dbind_const (μ₁ : Distr α) (μ₂ : Distr β) (h : ∑' a, μ₁ a = 1) :
    dbind (fun _ => μ₂) μ₁ = μ₂ := by
  ext b; simp [dbind_unfold_pmf, ENNReal.tsum_mul_right, h]

/-! ## Interplay of bind and return -/

section monadic

/-- Rocq: `dret_id_right_pmf`. -/
theorem dret_id_right_pmf (μ : Distr α) (a : α) : (μ ≫= fun a => dret a) a = μ a := by
  classical
  simp only [dbind_unfold_pmf, dret_pmf_unfold, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single a (fun b hb => by simp [Ne.symm hb])]; simp

/-- Rocq: `dret_id_right`. -/
@[simp] theorem dret_id_right (μ : Distr α) : (μ ≫= fun a => dret a) = μ :=
  distr_ext (dret_id_right_pmf μ)

/-- Rocq: `dret_id_left_pmf`. -/
theorem dret_id_left_pmf (f : α → Distr β) (a : α) (b : β) : (dret a ≫= f) b = f a b := by
  classical
  simp only [dbind_unfold_pmf, dret_pmf_unfold, ite_mul, one_mul, zero_mul]
  rw [tsum_eq_single a (fun b hb => by simp [hb])]; simp

/-- Rocq: `dret_id_left`. -/
@[simp] theorem dret_id_left (f : α → Distr β) (a : α) : (dret a ≫= f) = f a :=
  distr_ext (dret_id_left_pmf f a)

/-- Rocq: `dret_id_left'`. -/
theorem dret_id_left' (f : α → Distr β) (a : α) : (dret a ≫= f) = f a := dret_id_left f a

/-- Rocq: `dret_const`. -/
theorem dret_const (μ : Distr α) (b : β) (h : ∑' a, μ a = 1) : (μ ≫= fun _ => dret b) = dret b :=
  dbind_const μ (dret b) h

/-- Rocq: `dbind_dret_pmf_map`. -/
theorem dbind_dret_pmf_map (μ : Distr α) (a : α) (f : α → β) (hf : Function.Injective f) :
    (μ ≫= fun a' => dret (f a')) (f a) = μ a := by
  classical
  simp only [dbind_unfold_pmf, dret_pmf_unfold, hf.eq_iff, mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single a (fun b hb => by simp [Ne.symm hb])]; simp

/-- Rocq: `dbind_dret_pmf_map_ne`. -/
theorem dbind_dret_pmf_map_ne (μ : Distr α) (b : β) (f : α → β)
    (h : ¬ ∃ a, 0 < μ a ∧ f a = b) : (μ ≫= fun a => dret (f a)) b = 0 := by
  simp only [dbind_unfold_pmf]
  refine ENNReal.tsum_eq_zero.2 fun a => ?_
  by_cases hb : b = f a
  · have : μ a = 0 := pmf_eq_0_not_gt_0 μ a fun hμ => h ⟨a, hμ, hb.symm⟩
    simp [this]
  · simp [dret_0 _ _ hb]

/-- Rocq: `dbind_assoc_pmf`. -/
theorem dbind_assoc_pmf (f : α → Distr β) (g : β → Distr γ) (μ : Distr α) (c : γ) :
    (μ ≫= fun a => f a ≫= g) c = ((μ ≫= f) ≫= g) c := by
  simp only [dbind_unfold_pmf]
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc]

/-- Rocq: `dbind_assoc`. -/
theorem dbind_assoc (f : α → Distr β) (g : β → Distr γ) (μ : Distr α) :
    (μ ≫= fun a => f a ≫= g) = ((μ ≫= f) ≫= g) :=
  distr_ext (dbind_assoc_pmf f g μ)

/-- Rocq: `dbind_assoc'`. -/
theorem dbind_assoc' (f : α → Distr β) (g : β → Distr γ) (μ : Distr α) :
    μ ≫= (fun a => f a ≫= g) = (μ ≫= f) ≫= g := dbind_assoc f g μ

/-- Rocq: `dbind_comm`. -/
theorem dbind_comm (f : α → β → Distr γ) (μ₁ : Distr α) (μ₂ : Distr β) :
    (μ₁ ≫= fun a => μ₂ ≫= fun b => f a b) = (μ₂ ≫= fun b => μ₁ ≫= fun a => f a b) := by
  ext c
  simp only [dbind_unfold_pmf]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1; funext b; congr 1; funext a
  ring

/-- Rocq: `dbind_pos`. -/
theorem dbind_pos (f : α → Distr β) (μ : Distr α) (b : β) :
    0 < dbind f μ b ↔ ∃ a, 0 < f a b ∧ 0 < μ a := by
  simp only [dbind_unfold_pmf, pos_iff_ne_zero, ne_eq, ENNReal.tsum_eq_zero, not_forall,
    mul_eq_zero, not_or]
  constructor
  · rintro ⟨a, h1, h2⟩; exact ⟨a, h2, h1⟩
  · rintro ⟨a, h1, h2⟩; exact ⟨a, h2, h1⟩

/-- Rocq: `dbind_eq`. -/
theorem dbind_eq (f g : α → Distr β) (μ₁ μ₂ : Distr α) (hfg : ∀ a, 0 < μ₁ a → f a = g a)
    (hμ : ∀ a, μ₁ a = μ₂ a) : dbind f μ₁ = dbind g μ₂ := by
  rw [← distr_ext hμ]
  exact dbind_ext_right_strong μ₁ f g hfg

/-- Rocq: `dbind_mass`. -/
theorem dbind_mass (μ : Distr α) (f : α → Distr β) :
    ∑' b, (μ ≫= f) b = ∑' a, μ a * ∑' b, f a b := by
  simp only [dbind_unfold_pmf]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

/-- Rocq: `dbind_inhabited`. -/
theorem dbind_inhabited (f : α → Distr β) (μ : Distr α) (hμ : 0 < ∑' a, μ a)
    (hf : ∀ a, 0 < ∑' b, f a b) : 0 < ∑' b, dbind f μ b := by
  rw [dbind_mass]
  obtain ⟨a, ha⟩ := SeriesC_gtz_ex _ hμ
  exact SeriesC_pos _ a (ENNReal.mul_pos ha.ne' (hf a).ne')

/-- Rocq: `dbind_inhabited_ex`. -/
theorem dbind_inhabited_ex (f : α → Distr β) (μ : Distr α)
    (h : ∃ a, 0 < μ a ∧ 0 < ∑' b, f a b) : 0 < ∑' b, dbind f μ b := by
  rw [dbind_mass]
  obtain ⟨a, ha, hfa⟩ := h
  exact SeriesC_pos _ a (ENNReal.mul_pos ha.ne' hfa.ne')

/-- Rocq: `dbind_dret_pair_left`. -/
theorem dbind_dret_pair_left {α' : Type*} [Countable α'] (μ : Distr α) (a' : α') (b : α) :
    (μ ≫= fun a => dret (a, a')) (b, a') = μ b := by
  classical
  simp only [dbind_unfold_pmf, dret_pmf_unfold, Prod.mk.injEq, and_true, mul_ite, mul_one,
    mul_zero]
  rw [tsum_eq_single b (fun c hc => by simp [Ne.symm hc])]; simp

/-- Rocq: `dbind_dret_pair_right`. -/
theorem dbind_dret_pair_right {α' : Type*} [Countable α'] (μ : Distr α') (a : α) (b : α') :
    (μ ≫= fun a' => dret (a, a')) (a, b) = μ b := by
  classical
  simp only [dbind_unfold_pmf, dret_pmf_unfold, Prod.mk.injEq, true_and, mul_ite, mul_one,
    mul_zero]
  rw [tsum_eq_single b (fun c hc => by simp [Ne.symm hc])]; simp

/-- Rocq: `dbind_det`. -/
theorem dbind_det (μ : Distr α) (f : α → Distr β) (hμ : ∑' a, μ a = 1)
    (hf : ∀ a, 0 < μ a → ∑' b, f a b = 1) : ∑' b, (μ ≫= f) b = 1 := by
  rw [dbind_mass, ← hμ]
  congr 1; funext a
  rcases eq_or_ne (μ a) 0 with h0 | h0
  · simp [h0]
  · rw [hf a (pos_iff_ne_zero.2 h0), mul_one]

/-- Rocq: `dbind_det_inv_l`. -/
theorem dbind_det_inv_l (μ₁ : Distr α) (f : α → Distr β) (b : β) (h : (μ₁ ≫= f) b = 1) :
    ∑' a, μ₁ a = 1 := by
  refine le_antisymm μ₁.mass_le_one ?_
  rw [← h, dbind_unfold_pmf]
  exact ENNReal.tsum_le_tsum fun a => mul_le_of_le_one_right zero_le (pmf_le_1 _ _)

/-- Rocq: `dbind_det_inv_r`. -/
theorem dbind_det_inv_r (μ₁ : Distr α) (f : α → Distr β) (b : β) (h : (μ₁ ≫= f) b = 1) :
    ∀ a, 0 < μ₁ a → f a b = 1 := by
  intro a ha
  by_contra hne
  have hlt : f a b < 1 := lt_of_le_of_ne (pmf_le_1 _ _) hne
  have : ∑' a, μ₁ a * f a b < ∑' a, μ₁ a * 1 := by
    refine ENNReal.tsum_lt_tsum (i := a) ?_ ?_ ?_
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_refl _)
    · exact fun a' => mul_le_mul_right (pmf_le_1 _ _) _
    · exact ENNReal.mul_lt_mul_right ha.ne' (pmf_ne_top _ _) hlt
  rw [← dbind_unfold_pmf, h] at this
  simp only [mul_one] at this
  exact absurd μ₁.mass_le_one (not_le.2 this)

/-- Rocq: `dbind_Sup_seq`. -/
theorem dbind_Sup_seq (f : ℕ → α → Distr β) (f' : α → Distr β) (μ : Distr α) (b : β)
    (h1 : ∀ a, f' a b = ⨆ n, f n a b) (h2 : ∀ n a, f n a b ≤ f (n + 1) a b) :
    (μ ≫= f') b = ⨆ n, (μ ≫= fun a => f n a) b := by
  simp only [dbind_unfold_pmf, h1, ENNReal.mul_iSup]
  exact tsum_iSup_of_monotone fun a =>
    monotone_nat_of_le_succ fun n => mul_le_mul_right (h2 n a) _

end monadic

/-! ## Probabilities of (boolean) events -/

section probabilities

/-- Rocq: `prob`. -/
def prob (μ : Distr α) (P : α → Bool) : ℝ≥0∞ := ∑' a, if P a then μ a else 0

/-- Rocq: `prob_le_1`. -/
theorem prob_le_1 (μ : Distr α) (P : α → Bool) : prob μ P ≤ 1 :=
  (ENNReal.tsum_le_tsum fun a => by split_ifs <;> simp).trans μ.mass_le_one

/-- Rocq: `prob_ge_0` (trivial in `ℝ≥0∞`). -/
theorem prob_ge_0 (μ : Distr α) (P : α → Bool) : 0 ≤ prob μ P := zero_le

/-- Rocq: `prob_dret_true`. -/
theorem prob_dret_true (a : α) (P : α → Bool) (h : P a = true) : prob (dret a) P = 1 := by
  classical
  rw [prob, tsum_eq_single a (fun b hb => by simp [dret_0 _ _ hb])]
  simp [h, dret_1_1]

/-- Rocq: `prob_dret_false`. -/
theorem prob_dret_false (a : α) (P : α → Bool) (h : P a = false) : prob (dret a) P = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun b => ?_
  by_cases hb : b = a
  · subst hb; simp [h]
  · simp [dret_0 _ _ hb]

/-- Rocq: `prob_dbind`. -/
theorem prob_dbind (μ : Distr α) (f : α → Distr β) (P : β → Bool) :
    prob (dbind f μ) P = ∑' a, μ a * prob (f a) P := by
  simp only [prob, dbind_unfold_pmf]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1; funext b
  split_ifs <;> simp

/-- Rocq: `union_bound`. -/
theorem union_bound (μ : Distr α) (P Q : α → Bool) :
    prob μ (fun a => P a || Q a) ≤ prob μ P + prob μ Q := by
  simp only [prob]
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun a => by
    by_cases hP : P a <;> by_cases hQ : Q a <;> simp [hP, hQ]

/-- Rocq: `prob_Sup_seq`. -/
theorem prob_Sup_seq (μ : Distr α) (μ' : ℕ → Distr α) (ϕ : α → Bool)
    (h1 : ∀ a, μ a = ⨆ n, μ' n a) (h2 : ∀ n a, μ' n a ≤ μ' (n + 1) a) :
    prob μ ϕ = ⨆ n, prob (μ' n) ϕ := by
  simp only [prob]
  rw [← tsum_iSup_of_monotone]
  · congr 1; funext a
    cases ϕ a <;> simp [h1]
  · intro a
    refine monotone_nat_of_le_succ fun n => ?_
    cases ϕ a <;> simp [h2]

end probabilities

/-! ## Probabilities of decidable propositions -/

section probabilities_prop

/-- Rocq: `probp`. -/
def probp (μ : Distr α) (P : α → Prop) [DecidablePred P] : ℝ≥0∞ :=
  ∑' a, if P a then μ a else 0

variable (μ : Distr α) (P : α → Prop) [DecidablePred P]

/-- Rocq: `probp_le_1`. -/
theorem probp_le_1 : probp μ P ≤ 1 :=
  (ENNReal.tsum_le_tsum fun a => by split_ifs <;> simp).trans μ.mass_le_one

/-- Rocq: `probp_ge_0` (trivial in `ℝ≥0∞`). -/
theorem probp_ge_0 : 0 ≤ probp μ P := zero_le

end probabilities_prop

section probability_prop_lemmas

/-- Rocq: `probp_dret_true`. -/
theorem probp_dret_true (a : α) (P : α → Prop) [DecidablePred P] (h : P a) :
    probp (dret a) P = 1 := by
  rw [probp, tsum_eq_single a (fun b hb => by simp [dret_0 _ _ hb])]
  simp [h, dret_1_1]

/-- Rocq: `probp_dret_false`. -/
theorem probp_dret_false (a : α) (P : α → Prop) [DecidablePred P] (h : ¬ P a) :
    probp (dret a) P = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun b => ?_
  by_cases hb : b = a
  · subst hb; simp [h]
  · simp [dret_0 _ _ hb]

/-- Rocq: `probp_dbind`. -/
theorem probp_dbind (μ : Distr α) (f : α → Distr β) (P : β → Prop) [DecidablePred P] :
    probp (dbind f μ) P = ∑' a, μ a * probp (f a) P := by
  simp only [probp, dbind_unfold_pmf]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1; funext b
  split_ifs <;> simp

/-- Rocq: `union_bound_prop`. -/
theorem union_bound_prop (μ : Distr α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    probp μ (fun a => P a ∨ Q a) ≤ probp μ P + probp μ Q := by
  simp only [probp]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hP : P a <;> by_cases hQ : Q a <;> simp [hP, hQ]

end probability_prop_lemmas

/-! ## Subset distributions -/

section subset_distribution

variable (P : α → Bool)

/-- Rocq: `ssd_pmf`. -/
def ssd_pmf (μ : Distr α) : α → ℝ≥0∞ := fun a => if P a then μ a else 0

/-- Rocq: `ssd`. -/
def ssd (μ : Distr α) : Distr α where
  pmf := ssd_pmf P μ
  mass_le_one := (ENNReal.tsum_le_tsum fun a => by simp only [ssd_pmf]; split_ifs <;> simp).trans
    μ.mass_le_one

theorem ssd_apply (μ : Distr α) (a : α) : ssd P μ a = if P a then μ a else 0 := rfl

end subset_distribution

section subset_distribution_lemmas

/-- Rocq: `ssd_ret_pos`. -/
theorem ssd_ret_pos (P : α → Bool) (μ : Distr α) (a : α) (h : 0 < ssd P μ a) : P a = true := by
  rw [ssd_apply] at h
  by_contra hP; simp [hP] at h

/-- Rocq: `ssd_sum`. -/
theorem ssd_sum (P : α → Bool) (μ : Distr α) (a : α) :
    μ a = ssd P μ a + ssd (fun a => !P a) μ a := by
  simp only [ssd_apply]; cases P a <;> simp

/-- Rocq: `ssd_remove`. -/
theorem ssd_remove (P : α → Bool) (μ : Distr α) (h : ∀ a, (!P a) = true → μ a = 0) :
    ssd P μ = μ := by
  ext a; rw [ssd_apply]
  cases hP : P a
  · simp [h a (by simp [hP])]
  · simp

end subset_distribution_lemmas

section bind_lemmas

/-- Rocq: `bind_split_sum`. -/
theorem bind_split_sum (μ μ₁ μ₂ : Distr α) (ν : α → Distr β) (h : ∀ a, μ a = μ₁ a + μ₂ a) :
    ∀ b, (μ ≫= fun a' => ν a') b = (μ₁ ≫= fun a' => ν a') b + (μ₂ ≫= fun a' => ν a') b := by
  intro b
  simp only [dbind_unfold_pmf, h, add_mul, ENNReal.tsum_add]

/-- Rocq: `ssd_bind_split_sum`. -/
theorem ssd_bind_split_sum (μ : Distr α) (ν : α → Distr β) (P : α → Bool) :
    ∀ b, (μ ≫= fun a' => ν a') b =
      (ssd P μ ≫= fun a' => ν a') b + (ssd (fun a => !P a) μ ≫= fun a' => ν a') b :=
  bind_split_sum _ _ _ _ (ssd_sum P μ)

/-- Rocq: `ssd_bind_constant`. -/
theorem ssd_bind_constant (P : α → Bool) (μ : Distr α) (ν : α → Distr β) (b : β) (k : ℝ≥0∞)
    (h : ∀ a, P a = true → ν a b = k) :
    (ssd P μ ≫= fun a' => ν a') b = k * ∑' a, ssd P μ a := by
  rw [dbind_unfold_pmf, ← ENNReal.tsum_mul_left]
  congr 1; funext a
  rw [ssd_apply]
  cases hP : P a
  · simp
  · simp [h a hP, mul_comm]

/-- Rocq: `ssd_fix_value`. -/
theorem ssd_fix_value [DecidableEq α] (μ : Distr α) (v : α) :
    ∑' a, ssd (fun a => decide (a = v)) μ a = μ v := by
  simp only [ssd_apply, decide_eq_true_eq]
  rw [tsum_eq_single v (fun b hb => by simp [hb])]; simp

/-- Rocq: `ssd_chain`. -/
theorem ssd_chain (μ : Distr α) (P Q : α → Bool) :
    ssd P (ssd Q μ) = ssd (fun a => P a && Q a) μ := by
  ext a; simp only [ssd_apply]; cases P a <;> cases Q a <;> simp

end bind_lemmas

/-! ## Expected values -/

section exp_val

/-- Rocq: `Expval`. Functions take values in `ℝ≥0∞`; `ex_expval` is not needed. -/
def Expval (μ : Distr α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, μ a * f a

end exp_val

section exp_val_prop

/-- Rocq: `Expval_support`. -/
theorem Expval_support (μ : Distr α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) [DecidablePred fun a => 0 < μ a] :
    Expval μ f = Expval μ (fun a => if 0 < μ a then f a else c) := by
  simp only [Expval]
  congr 1; funext a
  split_ifs with h
  · rfl
  · simp [pmf_eq_0_not_gt_0 μ a h]

/-- Rocq: `Expval_dret`. -/
@[simp] theorem Expval_dret (f : α → ℝ≥0∞) (a : α) : Expval (dret a) f = f a := by
  rw [Expval, tsum_eq_single a (fun b hb => by simp [dret_0 _ _ hb])]
  simp [dret_1_1]

/-- Rocq: `Expval_const`. -/
theorem Expval_const (μ : Distr α) (c : ℝ≥0∞) : Expval μ (fun _ => c) = c * ∑' a, μ a := by
  rw [Expval, ENNReal.tsum_mul_right, mul_comm]

/-- Rocq: `Expval_le`. -/
theorem Expval_le (μ : Distr α) (f g : α → ℝ≥0∞) (h : ∀ x, f x ≤ g x) :
    Expval μ f ≤ Expval μ g :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_right (h a) _

/-- Rocq: `Expval_bounded`. -/
theorem Expval_bounded (μ : Distr α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ x, f x ≤ c) :
    Expval μ f ≤ c :=
  (Expval_le μ f _ h).trans <| by
    rw [Expval_const]; exact mul_le_of_le_one_right zero_le μ.mass_le_one

/-- Rocq: `Expval_dbind` (no positivity or summability side conditions in `ℝ≥0∞`). -/
theorem Expval_dbind (μ : Distr α) (k : α → Distr β) (f : β → ℝ≥0∞) :
    Expval (μ ≫= k) f = Expval μ (fun a => Expval (k a) f) := by
  simp only [Expval, dbind_unfold_pmf]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc]

/-- Rocq: `Expval_scal_l`. -/
theorem Expval_scal_l (μ : Distr α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    Expval μ (fun x => c * f x) = c * Expval μ f := by
  simp only [Expval, ← ENNReal.tsum_mul_left]
  congr 1; funext a; ring

/-- Rocq: `Expval_scal_r`. -/
theorem Expval_scal_r (μ : Distr α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    Expval μ (fun x => f x * c) = Expval μ f * c := by
  simp only [Expval, ← ENNReal.tsum_mul_right]
  congr 1; funext a; ring

/-- Rocq: `Expval_plus`. -/
theorem Expval_plus (μ : Distr α) (f g : α → ℝ≥0∞) :
    Expval μ (fun x => f x + g x) = Expval μ f + Expval μ g := by
  simp only [Expval, mul_add, ENNReal.tsum_add]

/-- Rocq: `Expval_ge_0` (trivial in `ℝ≥0∞`). -/
theorem Expval_ge_0 (μ : Distr α) (f : α → ℝ≥0∞) : 0 ≤ Expval μ f := zero_le

/-- Rocq: `Expval_ge_0'` (trivial in `ℝ≥0∞`; the non-negativity hypothesis is kept so that
downstream ports translate mechanically). -/
theorem Expval_ge_0' (μ : Distr α) (f : α → ℝ≥0∞) (_ : ∀ a, 0 ≤ f a) : 0 ≤ Expval μ f :=
  zero_le

/-- Rocq: `Expval_convex_le`. -/
theorem Expval_convex_le (μ : Distr α) (f : α → ℝ≥0∞) (r : ℝ≥0∞) (h : ∀ a, r ≤ f a)
    (hμ : ∑' a, μ a = 1) : r ≤ Expval μ f := by
  have := Expval_le μ (fun _ => r) f h
  rwa [Expval_const, hμ, mul_one] at this

/-- Auxiliary strict version used by `Expval_convex_lt` and `Expval_convex_ex_le`. -/
theorem Expval_convex_lt_aux (μ : Distr α) (f : α → ℝ≥0∞) (r : ℝ≥0∞)
    (h : ∀ a, 0 < μ a → r < f a) (hμ : ∑' a, μ a = 1) : r < Expval μ f := by
  obtain ⟨a0, ha0⟩ := SeriesC_gtz_ex μ.pmf (by rw [hμ]; exact one_pos)
  have hr : r ≠ ∞ := ne_top_of_lt (h a0 ha0)
  have : Expval μ (fun _ => r) < Expval μ f := by
    refine ENNReal.tsum_lt_tsum (i := a0) ?_ ?_ ?_
    · rw [ENNReal.tsum_mul_right, hμ, one_mul]; exact hr
    · intro a
      rcases eq_or_ne (μ a) 0 with h0 | h0
      · simp [h0]
      · exact mul_le_mul_right (h a (pos_iff_ne_zero.2 h0)).le _
    · exact ENNReal.mul_lt_mul_right ha0.ne' (pmf_ne_top _ _) (h a0 ha0)
  rwa [Expval_const, hμ, mul_one] at this

/-- Rocq: `Expval_convex_lt`. -/
theorem Expval_convex_lt (μ : Distr α) (f : α → ℝ≥0∞) (r : ℝ≥0∞) (h : ∀ a, r < f a)
    (hμ : ∑' a, μ a = 1) : r < Expval μ f :=
  Expval_convex_lt_aux μ f r (fun a _ => h a) hμ

/-- Rocq: `Expval_convex_ex_le`. -/
theorem Expval_convex_ex_le (μ : Distr α) (f : α → ℝ≥0∞) (r : ℝ≥0∞) (hμ : ∑' a, μ a = 1)
    (hle : Expval μ f ≤ r) : ∃ a', 0 < μ a' ∧ f a' ≤ r := by
  by_contra H
  push Not at H
  exact absurd hle (not_le.2 (Expval_convex_lt_aux μ f r H hμ))

/-- Rocq: `Expval_convex_ge`. -/
theorem Expval_convex_ge (μ : Distr α) (f : α → ℝ≥0∞) (r : ℝ≥0∞) (h : ∀ a, f a ≤ r)
    (_hμ : ∑' a, μ a = 1) : Expval μ f ≤ r :=
  Expval_bounded μ f r h

/-- Rocq: `markov_ineq`. -/
theorem markov_ineq (μ : Distr α) (f : α → ℝ≥0∞) (r : ℝ≥0∞) :
    r * Expval μ (fun a => if r ≤ f a then 1 else 0) ≤ Expval μ f := by
  rw [← Expval_scal_l]
  refine Expval_le μ _ _ fun a => ?_
  split_ifs with h <;> simp [h]

end exp_val_prop

/-! ## Monadic map -/

/-- Rocq: `dmap`. -/
def dmap (f : α → β) (μ : Distr α) : Distr β := μ ≫= fun a => dret (f a)

section dmap

/-- Rocq: `dmap_id`. -/
@[simp] theorem dmap_id (μ : Distr α) : dmap (fun x => x) μ = μ := dret_id_right μ

/-- Rocq: `dmap_unfold_pmf`. -/
theorem dmap_unfold_pmf [DecidableEq β] (f : α → β) (μ : Distr α) (b : β) :
    dmap f μ b = ∑' a, μ a * (if b = f a then 1 else 0) := by
  simp only [dmap, dbind_unfold_pmf, dret_pmf_unfold]

/-- Rocq: `dmap_fold`. -/
theorem dmap_fold (f : α → β) (μ : Distr α) : (μ ≫= fun a => dret (f a)) = dmap f μ := rfl

/-- Rocq: `dmap_dret_pmf`. -/
theorem dmap_dret_pmf (f : α → β) (a : α) (b : β) : dmap f (dret a) b = dret (f a) b := by
  rw [dmap, dret_id_left_pmf]

/-- Rocq: `dmap_dret`. -/
@[simp] theorem dmap_dret (f : α → β) (a : α) : dmap f (dret a) = dret (f a) :=
  distr_ext (dmap_dret_pmf f a)

/-- Rocq: `dmap_dbind_pmf`. -/
theorem dmap_dbind_pmf (f : β → γ) (g : α → Distr β) (μ : Distr α) (x : γ) :
    dmap f (dbind g μ) x = dbind (fun a => dmap f (g a)) μ x := by
  rw [dmap, ← dbind_assoc_pmf]; rfl

/-- Rocq: `dmap_dbind`. -/
theorem dmap_dbind (f : β → γ) (g : α → Distr β) (μ : Distr α) :
    dmap f (dbind g μ) = dbind (fun a => dmap f (g a)) μ :=
  distr_ext (dmap_dbind_pmf f g μ)

/-- Rocq: `dmap_comp`. -/
theorem dmap_comp (f : α → β) (g : β → δ) (μ : Distr α) :
    dmap g (dmap f μ) = dmap (g ∘ f) μ := by
  simp only [dmap]; rw [← dbind_assoc]; simp only [dret_id_left]; rfl

/-- Rocq: `dmap_eq`. -/
theorem dmap_eq (f g : α → β) (μ₁ μ₂ : Distr α) (hfg : ∀ a, 0 < μ₁ a → f a = g a)
    (hμ : ∀ a, μ₁ a = μ₂ a) : dmap f μ₁ = dmap g μ₂ :=
  dbind_eq _ _ _ _ (fun a ha => by rw [hfg a ha]) hμ

/-- Rocq: `dmap_eq_pmf`. -/
theorem dmap_eq_pmf (f g : α → β) (μ₁ μ₂ : Distr α) (x : β)
    (hfg : ∀ a, 0 < μ₁ a → f a = g a) (hμ : ∀ a, μ₁ a = μ₂ a) : dmap f μ₁ x = dmap g μ₂ x := by
  rw [dmap_eq f g μ₁ μ₂ hfg hμ]

/-- Rocq: `dmap_mass`. -/
@[simp] theorem dmap_mass (μ : Distr α) (f : α → β) : ∑' b, dmap f μ b = ∑' a, μ a := by
  rw [dmap, dbind_mass]; simp

/-- Rocq: `dmap_pos`. -/
theorem dmap_pos (μ : Distr α) (f : α → β) (b : β) :
    0 < dmap f μ b ↔ ∃ a, b = f a ∧ 0 < μ a := by
  rw [dmap, dbind_pos]
  constructor
  · rintro ⟨a, h1, h2⟩; exact ⟨a, dret_pos _ _ h1, h2⟩
  · rintro ⟨a, rfl, h2⟩; exact ⟨a, by rw [dret_1_1 _ _ rfl]; exact one_pos, h2⟩

/-- Rocq: `dmap_elem_eq`. -/
theorem dmap_elem_eq (μ : Distr α) (a : α) (b : β) (f : α → β) (hf : Function.Injective f)
    (h : b = f a) : dmap f μ b = μ a := by
  subst h; exact dbind_dret_pmf_map μ a f hf

/-- Rocq: `dmap_elem_ne`. -/
theorem dmap_elem_ne (μ : Distr α) (b : β) (f : α → β) (h : ¬ ∃ a, 0 < μ a ∧ f a = b) :
    dmap f μ b = 0 :=
  dbind_dret_pmf_map_ne μ b f h

/-- Rocq: `dmap_rearrange`. -/
theorem dmap_rearrange (μ₁ μ₂ : Distr α) (f : α → α) (hf : Function.Injective f)
    (hcov : ∀ a, 0 < μ₁ a → ∃ a', f a' = a) (hμ : ∀ a, μ₁ (f a) = μ₂ a) : μ₁ = dmap f μ₂ := by
  ext a
  by_cases h : ∃ a', f a' = a
  · obtain ⟨a', rfl⟩ := h
    rw [dmap_elem_eq μ₂ a' _ f hf rfl, hμ]
  · rw [dmap_elem_ne]
    · exact pmf_eq_0_not_gt_0 μ₁ a fun h' => h (hcov a h')
    · rintro ⟨a', -, ha'⟩; exact h ⟨a', ha'⟩

/-- Rocq: `Expval_dmap`. -/
theorem Expval_dmap (μ : Distr α) (f : α → β) (g : β → ℝ≥0∞) :
    Expval (dmap f μ) g = Expval μ (g ∘ f) := by
  rw [dmap, Expval_dbind]; simp only [Expval_dret]; rfl

/-- Rocq: `prob_dmap`. -/
theorem prob_dmap (μ : Distr α) (f : α → β) (P : β → Bool) :
    prob (dmap f μ) P = prob μ (fun a => P (f a)) := by
  rw [dmap, prob_dbind]
  congr 1; funext a
  cases h : P (f a)
  · simp [prob_dret_false _ _ h, h]
  · simp [prob_dret_true _ _ h, h]

end dmap

/-- Rocq: `dbind_dmap_inj_rearrange`. The injectivity hypotheses of the Rocq statement are not
needed. -/
theorem dbind_dmap_inj_rearrange (μ : Distr α) (μ' : Distr γ) (f : α → β) (g : β × γ → δ) :
    (dmap f μ ≫= fun b => dmap (fun c => g (b, c)) μ') =
      (μ ≫= fun a => dmap (fun c => g (f a, c)) μ') := by
  rw [dmap, ← dbind_assoc]; simp only [dret_id_left]

/-! ## Monadic strength -/

/-- Rocq: `strength_l`. -/
def strength_l (a : α) (μ : Distr β) : Distr (α × β) := dmap (fun b => (a, b)) μ

/-- Rocq: `strength_r`. -/
def strength_r (μ : Distr α) (b : β) : Distr (α × β) := dmap (fun a => (a, b)) μ

/-- Rocq: `dbind_strength_l`. -/
theorem dbind_strength_l (f : α × β → Distr δ) (a : α) (μ : Distr β) :
    (strength_l a μ ≫= f) = (μ ≫= fun b => f (a, b)) := by
  rw [strength_l, dmap, ← dbind_assoc]; simp only [dret_id_left]

/-- Rocq: `dbind_strength_r`. -/
theorem dbind_strength_r (f : α × β → Distr δ) (μ : Distr α) (b : β) :
    (strength_r μ b ≫= f) = (μ ≫= fun a => f (a, b)) := by
  rw [strength_r, dmap, ← dbind_assoc]; simp only [dret_id_left]

/-- Rocq: `strength_l_dbind`. -/
theorem strength_l_dbind (f : β → Distr δ) (a : α) (μ : Distr β) :
    strength_l a (dbind f μ) = (μ ≫= fun b => strength_l a (f b)) := by
  rw [strength_l, dmap_dbind]; rfl

/-- Rocq: `strength_r_dbind`. -/
theorem strength_r_dbind (f : α → Distr δ) (μ : Distr α) (b : β) :
    strength_r (dbind f μ) b = (μ ≫= fun a => strength_r (f a) b) := by
  rw [strength_r, dmap_dbind]; rfl

/-- Rocq: `strength_comm`. -/
theorem strength_comm (f : α → Distr α) (g : β → Distr β) (a : α) (b : β) :
    (strength_l a (g b) ≫= fun p => strength_r (f p.1) p.2) =
      (strength_r (f a) b ≫= fun p => strength_l p.1 (g p.2)) := by
  rw [dbind_strength_l, dbind_strength_r]
  simp only [strength_l, strength_r, dmap]
  exact dbind_comm (fun b' a' => dret (a', b')) (g b) (f a)

/-! ## Monadic fold left -/

/-- Rocq: `foldlM`. -/
def foldlM {ι : Type*} (f : β → ι → Distr β) (b : β) (xs : List ι) : Distr β :=
  List.foldr (fun a m b => f b a ≫= m) dret xs b

section foldlM

variable {ι : Type*}

/-- Rocq: `foldlM_nil`. -/
@[simp] theorem foldlM_nil (f : β → ι → Distr β) (b : β) : foldlM f b [] = dret b := rfl

/-- Rocq: `foldlM_cons`. -/
@[simp] theorem foldlM_cons (f : β → ι → Distr β) (b : β) (x : ι) (xs : List ι) :
    foldlM f b (x :: xs) = (f b x ≫= fun b' => foldlM f b' xs) := rfl

end foldlM

/-! ## Monadic iteration -/

/-- Rocq: `iterM`. -/
def iterM : ℕ → (α → Distr α) → α → Distr α
  | 0, _, a => dret a
  | n + 1, f, a => f a ≫= iterM n f

section iterM

/-- Rocq: `iterM_O`. -/
@[simp] theorem iterM_O (f : α → Distr α) (a : α) : iterM 0 f a = dret a := rfl

/-- Rocq: `iterM_Sn`. -/
theorem iterM_Sn (f : α → Distr α) (a : α) (n : ℕ) : iterM (n + 1) f a = (f a ≫= iterM n f) :=
  rfl

/-- Rocq: `iterM_plus`. -/
theorem iterM_plus (f : α → Distr α) (a : α) (n m : ℕ) :
    iterM (n + m) f a = (iterM n f a ≫= iterM m f) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_right_comm, iterM_Sn, iterM_Sn, ← dbind_assoc]
    exact dbind_ext_right _ _ _ ih

/-- Rocq: `iterM_mono`. -/
theorem iterM_mono (f g : α → Distr α) (n : ℕ) (a a' : α) (h : ∀ a a', f a a' ≤ g a a') :
    iterM n f a a' ≤ iterM n g a a' := by
  induction n generalizing a a' with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [iterM_Sn, dbind_unfold_pmf]
    exact ENNReal.tsum_le_tsum fun b => mul_le_mul' (h a b) (ih b a')

end iterM

/-! ## Coins -/

/-- Rocq: `fair_coin`. -/
def fair_coin : Distr Bool where
  pmf := fun _ => 2⁻¹
  mass_le_one := by rw [tsum_bool, ENNReal.inv_two_add_inv_two]

/-- Rocq: `fair_coin_mass`. -/
@[simp] theorem fair_coin_mass : ∑' b, fair_coin b = 1 := by
  show ∑' _ : Bool, (2⁻¹ : ℝ≥0∞) = 1
  rw [tsum_bool, ENNReal.inv_two_add_inv_two]

/-- Rocq: `fair_coin_pmf`. -/
@[simp] theorem fair_coin_pmf (b : Bool) : fair_coin b = 2⁻¹ := rfl

/-- Rocq: `fair_coin_dbind_mass`. -/
theorem fair_coin_dbind_mass (f : Bool → Distr α) :
    ∑' a, (fair_coin ≫= f) a = 2⁻¹ * ∑' a, f true a + 2⁻¹ * ∑' a, f false a := by
  rw [dbind_mass, tsum_bool, add_comm]; rfl

/-- Rocq: `Expval_fair_coin`. -/
theorem Expval_fair_coin (f : Bool → ℝ≥0∞) :
    Expval fair_coin f = 2⁻¹ * f true + 2⁻¹ * f false := by
  rw [Expval, tsum_bool, add_comm]; rfl

/-- Rocq: `biased_coin_pmf`. -/
def biased_coin_pmf (r : ℝ≥0∞) : Bool → ℝ≥0∞ := fun b => if b then r else 1 - r

/-- Rocq: `biased_coin`. -/
def biased_coin (r : ℝ≥0∞) (P : r ≤ 1) : Distr Bool where
  pmf := biased_coin_pmf r
  mass_le_one := by
    rw [tsum_bool]; simp only [biased_coin_pmf, Bool.false_eq_true, ite_false, ite_true]
    rw [tsub_add_cancel_of_le P]

/-- Rocq: `fair_conv_comb`. -/
def fair_conv_comb (μ₁ μ₂ : Distr α) : Distr α :=
  dbind (fun b => if b then μ₁ else μ₂) fair_coin

section conv_prop

/-- Rocq: `fair_conv_comb_pmf`. -/
theorem fair_conv_comb_pmf (μ₁ μ₂ : Distr α) (a : α) :
    fair_conv_comb μ₁ μ₂ a = 2⁻¹ * μ₁ a + 2⁻¹ * μ₂ a := by
  rw [fair_conv_comb, dbind_unfold_pmf, tsum_bool, add_comm]; rfl

/-- Rocq: `dbind_fair_conv_comb`. -/
theorem dbind_fair_conv_comb (f₁ f₂ : α → Distr β) (μ : Distr α) :
    (μ ≫= fun a => fair_conv_comb (f₁ a) (f₂ a)) = fair_conv_comb (μ ≫= f₁) (μ ≫= f₂) := by
  ext b
  simp only [fair_conv_comb_pmf, dbind_unfold_pmf, mul_add, ENNReal.tsum_add,
    ← ENNReal.tsum_mul_left]
  congr 1 <;> congr 1 <;> funext a <;> ring

/-- Rocq: `dbind_dret_coin_zero`. -/
theorem dbind_dret_coin_zero (f : Bool → α) (a : α) (h : ∀ b, f b ≠ a) :
    (fair_coin ≫= fun b => dret (f b)) a = 0 :=
  dbind_dret_pmf_map_ne _ _ _ fun ⟨b, _, hb⟩ => h b hb

/-- Rocq: `dbind_dret_coin_nonzero`. -/
theorem dbind_dret_coin_nonzero (f : Bool → α) (a : α) (hf : Function.Injective f)
    (h : ∃ b, f b = a) : (fair_coin ≫= fun b => dret (f b)) a = 2⁻¹ := by
  obtain ⟨b, rfl⟩ := h
  rw [dbind_dret_pmf_map _ _ _ hf]; rfl

/-- Rocq: `fair_conv_comb_mass`. -/
theorem fair_conv_comb_mass (μ₁ μ₂ : Distr α) :
    ∑' a, fair_conv_comb μ₁ μ₂ a = 2⁻¹ * (∑' a, μ₁ a + ∑' a, μ₂ a) := by
  simp only [fair_conv_comb_pmf, ENNReal.tsum_add, ENNReal.tsum_mul_left, mul_add]

end conv_prop

/-! ## The zero distribution -/

/-- Rocq: `dzero`. -/
def dzero : Distr α where
  pmf := fun _ => 0
  mass_le_one := by simp

section dzero

/-- Rocq: `distr_inhabited`. -/
instance : Inhabited (Distr α) := ⟨dzero⟩

/-- Rocq: `dzero_0`. -/
@[simp] theorem dzero_0 (a : α) : (dzero : Distr α) a = 0 := rfl

/-- Rocq: `dzero_ext`. -/
theorem dzero_ext (μ : Distr α) (h : ∀ a, μ a = 0) : μ = dzero := distr_ext h

/-- Rocq: `dzero_supp_empty`. -/
theorem dzero_supp_empty (a : α) : ¬ 0 < (dzero : Distr α) a := by simp

/-- Rocq: `dzero_mass`. -/
@[simp] theorem dzero_mass : ∑' a, (dzero : Distr α) a = 0 := by simp

/-- Rocq: `SeriesC_zero_dzero`. -/
theorem SeriesC_zero_dzero (μ : Distr α) (h : ∑' a, μ a = 0) : μ = dzero :=
  dzero_ext μ (ENNReal.tsum_eq_zero.1 h)

/-- Rocq: `not_dzero_gt_0`. -/
theorem not_dzero_gt_0 (μ : Distr α) (h : μ ≠ dzero) : 0 < ∑' a, μ a :=
  pos_iff_ne_zero.2 fun h' => h (SeriesC_zero_dzero μ h')

/-- Rocq: `dret_not_dzero`. -/
theorem dret_not_dzero (a : α) : dret a ≠ dzero := by
  intro h
  have : dret a a = (dzero : Distr α) a := by rw [h]
  rw [dret_1_1 a a rfl, dzero_0] at this
  exact one_ne_zero this

/-- Rocq: `dbind_dzero_pmf`. -/
theorem dbind_dzero_pmf (f : α → Distr β) (b : β) : (dzero ≫= fun a => f a) b = 0 := by
  simp [dbind_unfold_pmf]

/-- Rocq: `dzero_dbind_pmf`. -/
theorem dzero_dbind_pmf (μ : Distr α) (b : β) : (μ ≫= fun _ => dzero) b = (dzero : Distr β) b := by
  simp [dbind_unfold_pmf]

/-- Rocq: `dzero_dbind`. -/
@[simp] theorem dzero_dbind (μ : Distr α) : (μ ≫= fun _ => (dzero : Distr β)) = dzero :=
  distr_ext (dzero_dbind_pmf μ)

/-- Rocq: `dbind_dzero`. -/
@[simp] theorem dbind_dzero (f : α → Distr β) : (dzero ≫= fun a => f a) = dzero :=
  distr_ext (dbind_dzero_pmf f)

/-- Rocq: `dbind_dzero_strong`. -/
theorem dbind_dzero_strong (μ : Distr α) (f : α → Distr β) (h : ∀ a, 0 < μ a → f a = dzero) :
    (μ ≫= fun a => f a) = dzero := by
  rw [dbind_ext_right_strong μ f (fun _ => dzero) h, dzero_dbind]

/-- Rocq: `dmap_dzero`. -/
@[simp] theorem dmap_dzero (f : α → β) : dmap f (dzero : Distr α) = dzero := dbind_dzero _

/-- Rocq: `Expval_dzero`. -/
@[simp] theorem Expval_dzero (h : α → ℝ≥0∞) : Expval (dzero : Distr α) h = 0 := by
  simp [Expval]

end dzero

/-- Rocq: `dmap_dzero_inv`. -/
theorem dmap_dzero_inv (f : α → β) (μ : Distr α) (h : dmap f μ = dzero) : μ = dzero := by
  apply SeriesC_zero_dzero
  rw [← dmap_mass μ f, h, dzero_mass]

/-! ## Diagonal -/

open Classical in
/-- Rocq: `ddiag`. -/
def ddiag (μ : Distr α) : Distr (α × α) where
  pmf := fun p => if p.1 = p.2 then μ p.1 else 0
  mass_le_one := by
    rw [ENNReal.tsum_prod (f := fun a b => if a = b then μ a else 0)]
    simp only [SeriesC_singleton']
    exact μ.mass_le_one

/-- Rocq: `ddiag_pmf`. -/
theorem ddiag_pmf [DecidableEq α] (μ : Distr α) (p : α × α) :
    ddiag μ p = if p.1 = p.2 then μ p.1 else 0 := by
  simp only [ddiag, Distr.coe_mk]; congr

/-! ## Products -/

/-- Rocq: `dprod`. -/
def dprod (μ₁ : Distr α) (μ₂ : Distr β) : Distr (α × β) :=
  μ₁ ≫= fun a => μ₂ ≫= fun b => dret (a, b)

/-- Rocq: `dprod_pmf`. -/
theorem dprod_pmf (μ₁ : Distr α) (μ₂ : Distr β) (a : α) (b : β) :
    dprod μ₁ μ₂ (a, b) = μ₁ a * μ₂ b := by
  rw [dprod, dbind_unfold_pmf, tsum_eq_single a]
  · rw [dbind_dret_pair_right]
  · intro a' ha'
    rw [dbind_dret_pmf_map_ne, mul_zero]
    rintro ⟨b', -, hb'⟩; exact ha' (congrArg Prod.fst hb')

section dprod

variable (μ₁ : Distr α) (μ₂ : Distr β)

/-- Rocq: `dprod_pos`. -/
theorem dprod_pos (a : α) (b : β) : 0 < dprod μ₁ μ₂ (a, b) ↔ 0 < μ₁ a ∧ 0 < μ₂ b := by
  rw [dprod_pmf, CanonicallyOrderedAdd.mul_pos]

/-- Rocq: `dprod_mass`. -/
theorem dprod_mass : ∑' p, dprod μ₁ μ₂ p = (∑' a, μ₁ a) * ∑' b, μ₂ b := by
  rw [ENNReal.tsum_prod']
  simp only [dprod_pmf, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

end dprod

/-! ## Swap -/

/-- Rocq: `dswap`. -/
def dswap (μ : Distr (α × β)) : Distr (β × α) := dmap Prod.swap μ

/-- Rocq: `dswap_pos`. -/
theorem dswap_pos (μ : Distr (α × β)) (a : α) (b : β) (h : 0 < dswap μ (b, a)) :
    0 < μ (a, b) := by
  obtain ⟨⟨a', b'⟩, hp, hpos⟩ := (dmap_pos _ _ _).1 h
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact hpos

/-! ## Marginals -/

/-- Rocq: `lmarg`. -/
def lmarg (μ : Distr (α × β)) : Distr α := dmap Prod.fst μ

/-- Rocq: `rmarg`. -/
def rmarg (μ : Distr (α × β)) : Distr β := dmap Prod.snd μ

section marginals

/-- Rocq: `lmarg_pmf`. -/
theorem lmarg_pmf (μ : Distr (α × β)) (a : α) : lmarg μ a = ∑' b, μ (a, b) := by
  rw [lmarg, dmap, dbind_unfold_pmf, ENNReal.tsum_prod', tsum_eq_single a]
  · simp [dret_1_1]
  · intro a' ha'
    exact ENNReal.tsum_eq_zero.2 fun b => by simp [dret_0 _ _ (Ne.symm ha')]

/-- Rocq: `rmarg_pmf`. -/
theorem rmarg_pmf (μ : Distr (α × β)) (b : β) : rmarg μ b = ∑' a, μ (a, b) := by
  rw [rmarg, dmap, dbind_unfold_pmf, ENNReal.tsum_prod', ENNReal.tsum_comm, tsum_eq_single b]
  · simp [dret_1_1]
  · intro b' hb'
    exact ENNReal.tsum_eq_zero.2 fun a => by simp [dret_0 _ _ (Ne.symm hb')]

/-- Rocq: `lmarg_dprod_pmf`. -/
theorem lmarg_dprod_pmf (μ₁ : Distr α) (μ₂ : Distr β) (a : α) :
    lmarg (dprod μ₁ μ₂) a = μ₁ a * ∑' b, μ₂ b := by
  simp only [lmarg_pmf, dprod_pmf, ENNReal.tsum_mul_left]

/-- Rocq: `lmarg_dprod`. -/
theorem lmarg_dprod (μ₁ : Distr α) (μ₂ : Distr β) (h : ∑' b, μ₂ b = 1) :
    lmarg (dprod μ₁ μ₂) = μ₁ := by
  ext a; rw [lmarg_dprod_pmf, h, mul_one]

/-- Rocq: `lmarg_dswap`. -/
theorem lmarg_dswap (μ : Distr (α × β)) : lmarg (dswap μ) = rmarg μ := by
  rw [lmarg, dswap, dmap_comp]; rfl

/-- Rocq: `rmarg_dswap`. -/
theorem rmarg_dswap (μ : Distr (α × β)) : rmarg (dswap μ) = lmarg μ := by
  rw [rmarg, dswap, dmap_comp]; rfl

/-- Rocq: `rmarg_dprod_pmf`. -/
theorem rmarg_dprod_pmf (μ₁ : Distr α) (μ₂ : Distr β) (b : β) :
    rmarg (dprod μ₁ μ₂) b = μ₂ b * ∑' a, μ₁ a := by
  simp only [rmarg_pmf, dprod_pmf, ENNReal.tsum_mul_right, mul_comm]

/-- Rocq: `rmarg_dprod`. -/
theorem rmarg_dprod (μ₁ : Distr α) (μ₂ : Distr β) (h : ∑' a, μ₁ a = 1) :
    rmarg (dprod μ₁ μ₂) = μ₂ := by
  ext b; rw [rmarg_dprod_pmf, h, mul_one]

end marginals

/-- Rocq: `ddiag_lmarg`. -/
@[simp] theorem ddiag_lmarg (μ : Distr α) : lmarg (ddiag μ) = μ := by
  classical
  ext a; rw [lmarg_pmf]; simp only [ddiag_pmf]; simp

/-- Rocq: `ddiag_rmarg`. -/
@[simp] theorem ddiag_rmarg (μ : Distr α) : rmarg (ddiag μ) = μ := by
  classical
  ext a; rw [rmarg_pmf]; simp only [ddiag_pmf]
  rw [tsum_eq_single a (fun b hb => by simp [hb])]; simp

/-- Rocq: `lmarg_dzero`. -/
@[simp] theorem lmarg_dzero : lmarg (dzero : Distr (α × β)) = dzero := dmap_dzero _

/-- Rocq: `rmarg_dzero`. -/
@[simp] theorem rmarg_dzero : rmarg (dzero : Distr (α × β)) = dzero := dmap_dzero _

/-! ## Pointwise order -/

/-- Rocq: `distr_le`. -/
def distr_le (μ₁ μ₂ : Distr α) : Prop := ∀ a, μ₁ a ≤ μ₂ a

section order

/-- Rocq: `distr_le_dzero`. -/
theorem distr_le_dzero (μ : Distr α) : distr_le dzero μ := fun _ => zero_le

/-- Rocq: `distr_le_refl`. -/
theorem distr_le_refl (μ : Distr α) : distr_le μ μ := fun _ => le_rfl

/-- Rocq: `distr_le_trans`. -/
theorem distr_le_trans (μ₁ μ₂ μ₃ : Distr α) (h₁ : distr_le μ₁ μ₂) (h₂ : distr_le μ₂ μ₃) :
    distr_le μ₁ μ₃ := fun a => (h₁ a).trans (h₂ a)

/-- Rocq: `distr_le_antisym`. -/
theorem distr_le_antisym (μ₁ μ₂ : Distr α) (h₁ : distr_le μ₁ μ₂) (h₂ : distr_le μ₂ μ₁) :
    μ₁ = μ₂ := distr_ext fun a => le_antisymm (h₁ a) (h₂ a)

/-- Rocq: `distr_le_dbind`. -/
theorem distr_le_dbind (μ₁ μ₂ : Distr α) (f₁ f₂ : α → Distr β) (hle : distr_le μ₁ μ₂)
    (hf : ∀ a, distr_le (f₁ a) (f₂ a)) : distr_le (dbind f₁ μ₁) (dbind f₂ μ₂) := fun b =>
  ENNReal.tsum_le_tsum fun a => mul_le_mul' (hle a) (hf a b)

/-- Rocq: `distr_le_dmap_1`. -/
theorem distr_le_dmap_1 (μ₁ μ₂ : Distr α) (f : α → β) (h : distr_le μ₁ μ₂) :
    distr_le (dmap f μ₁) (dmap f μ₂) :=
  distr_le_dbind _ _ _ _ h fun _ => distr_le_refl _

/-- Rocq: `distr_le_dmap_2`. -/
theorem distr_le_dmap_2 (μ₁ μ₂ : Distr α) (f : α → β) (hf : Function.Injective f)
    (h : distr_le (dmap f μ₁) (dmap f μ₂)) : distr_le μ₁ μ₂ := fun a => by
  have := h (f a)
  rwa [dmap_elem_eq _ a _ f hf rfl, dmap_elem_eq _ a _ f hf rfl] at this

end order

/-! ## Scaled distribution -/

/-- Rocq: `distr_scal`. -/
def distr_scal (r : ℝ≥0∞) (μ : Distr α) (Hr : r * ∑' a, μ a ≤ 1) : Distr α where
  pmf := fun a => r * μ a
  mass_le_one := by rw [ENNReal.tsum_mul_left]; exact Hr

/-! ## Limit distribution -/

section convergence

/-- Rocq: `lim_distr`. -/
def lim_distr (h : ℕ → Distr α) (Hmon : ∀ n a, h n a ≤ h (n + 1) a) : Distr α where
  pmf := fun a => ⨆ n, h n a
  mass_le_one := by
    rw [tsum_iSup_of_monotone fun a => monotone_nat_of_le_succ fun n => Hmon n a]
    exact iSup_le fun n => (h n).mass_le_one

/-- Rocq: `lim_distr_pmf`. -/
theorem lim_distr_pmf (h : ℕ → Distr α) (Hmon : ∀ n a, h n a ≤ h (n + 1) a) (a : α) :
    lim_distr h Hmon a = ⨆ n, h n a := rfl

end convergence

/-! ## Uniform sampling -/

section uniform

/-- Rocq: `dunif`. For `N = 0` the type `Fin 0` is empty, so this is `dzero`. -/
def dunif (N : ℕ) : Distr (Fin N) where
  pmf := fun _ => (N : ℝ≥0∞)⁻¹
  mass_le_one := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_le_one _

/-- Rocq: `dunif_pmf`. -/
@[simp] theorem dunif_pmf (N : ℕ) (n : Fin N) : dunif N n = (N : ℝ≥0∞)⁻¹ := rfl

/-- Rocq: `dunif_mass`. -/
theorem dunif_mass (N : ℕ) (hN : N ≠ 0) : ∑' n, dunif N n = 1 := by
  simp only [dunif_pmf]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hN) (ENNReal.natCast_ne_top N)

/-- Rocq: `dmap_unif_zero`. -/
theorem dmap_unif_zero (N : ℕ) (f : Fin N → α) (a : α) (h : ∀ n, f n ≠ a) :
    dmap f (dunif N) a = 0 :=
  dmap_elem_ne _ _ _ fun ⟨n, _, hn⟩ => h n hn

/-- Rocq: `dmap_unif_nonzero`. -/
theorem dmap_unif_nonzero (N : ℕ) (n : Fin N) (f : Fin N → α) (a : α) (hf : Function.Injective f)
    (h : f n = a) : dmap f (dunif N) a = (N : ℝ≥0∞)⁻¹ :=
  dmap_elem_eq _ n a f hf h.symm

/-- Rocq: `dunif_fair_conv_comb`. -/
theorem dunif_fair_conv_comb : dunif 2 = fair_conv_comb (dret 1) (dret 0) := by
  ext n
  rw [dunif_pmf, fair_conv_comb_pmf]
  fin_cases n
  · simp [dret_0, dret_1_1]
  · simp [dret_0, dret_1_1]

/-- Rocq: `dunifP`. Uniform distribution on `Fin (N + 1)`, which is never `dzero`. -/
def dunifP (N : ℕ) : Distr (Fin (N + 1)) := dunif (N + 1)

@[simp] theorem dunifP_pmf (N : ℕ) (n : Fin (N + 1)) :
    dunifP N n = ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ := rfl

/-- Rocq: `dunifP_pos`. -/
theorem dunifP_pos (N : ℕ) (n : Fin (N + 1)) : 0 < dunifP N n := by
  rw [dunifP_pmf]; exact ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)

/-- Rocq: `dunifP_mass`. -/
@[simp] theorem dunifP_mass (N : ℕ) : ∑' n, dunifP N n = 1 := dunif_mass (N + 1) N.succ_ne_zero

/-- Rocq: `dunifP_not_dzero`. -/
theorem dunifP_not_dzero (N : ℕ) : dunifP N ≠ dzero := by
  intro h
  have := dunifP_mass N
  rw [h, dzero_mass] at this
  exact zero_ne_one this

/-- Rocq: `dunifP_decompose`. -/
theorem dunifP_decompose (N M x : ℕ) (f : Fin (N + 1) × Fin (M + 1) → Fin (x + 1))
    (hf : Function.Bijective f) (hx : x = (N + 1) * (M + 1) - 1) :
    dunifP x = (dunifP N ≫= fun n => dmap (fun m => f (n, m)) (dunifP M)) := by
  ext y
  obtain ⟨⟨n, m⟩, rfl⟩ := hf.2 y
  rw [dbind_unfold_pmf, tsum_eq_single n]
  · rw [dmap_elem_eq _ m _ _ (fun m₁ m₂ h => by simpa using hf.1 h) rfl]
    simp only [dunifP_pmf]
    have hx' : x + 1 = (N + 1) * (M + 1) := by
      subst hx; have : 0 < (N + 1) * (M + 1) := Nat.mul_pos (by omega) (by omega); omega
    rw [hx', Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]
  · intro n' hn'
    rw [dmap_elem_ne, mul_zero]
    rintro ⟨m', -, hm'⟩
    exact hn' (congrArg Prod.fst (hf.1 hm'))

open Classical in
/-- Rocq: `dunif_fragmented`. -/
theorem dunif_fragmented (N M : ℕ) (f : ℕ → ℕ) (hinj : Function.Injective f)
    (Hbound : ∀ n, n < M + 1 → f n < N + 1) (_hle : M ≤ N) :
    dunifP N = (dunifP N ≫= fun n : Fin (N + 1) =>
      if ∃ m : Fin (M + 1), f m = (n : ℕ) then
        dmap (fun m' : Fin (M + 1) => (⟨f m', Hbound _ m'.isLt⟩ : Fin (N + 1))) (dunifP M)
      else dret n) := by
  set F : Fin (M + 1) → Fin (N + 1) := fun m' => ⟨f m', Hbound _ m'.isLt⟩ with hFdef
  have hF : Function.Injective F := fun m₁ m₂ h => Fin.ext (hinj (congrArg Fin.val h))
  have hS : ∀ n' : Fin (N + 1), (∃ m : Fin (M + 1), f m = n') ↔ ∃ m, F m = n' := fun n' =>
    ⟨fun ⟨m, hm⟩ => ⟨m, Fin.ext hm⟩, fun ⟨m, hm⟩ => ⟨m, congrArg Fin.val hm⟩⟩
  ext n
  rw [dbind_unfold_pmf]
  simp only [dunifP_pmf]
  rw [ENNReal.tsum_mul_left]
  symm
  convert mul_one _ using 2
  by_cases hn : ∃ m, F m = n
  · have hval : dmap F (dunifP M) n = ((M + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      obtain ⟨m, rfl⟩ := hn; exact dmap_elem_eq _ m _ F hF rfl
    have : ∀ n' : Fin (N + 1),
        (if ∃ m : Fin (M + 1), f m = (n' : ℕ) then dmap F (dunifP M) else dret n') n =
        if ∃ m, F m = n' then ((M + 1 : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
      intro n'
      by_cases h' : ∃ m, F m = n'
      · rw [ite_eq_left ((hS n').2 h'), ite_eq_left h', hval]
      · rw [ite_eq_right (fun h => h' ((hS n').1 h)), ite_eq_right h']
        refine dret_0 _ _ fun h => h' (h ▸ hn)
    simp_rw [this]
    rw [← hF.tsum_eq]
    · simp only [exists_apply_eq_apply, ite_true]
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast M.succ_ne_zero)
        (ENNReal.natCast_ne_top _)
    · intro n' hn'
      by_contra h'
      exact hn' (ite_eq_right h')
  · rw [tsum_eq_single n]
    · rw [ite_eq_right (fun h => hn ((hS n).1 h)), dret_1_1 _ _ rfl]
    · intro n' hn'
      by_cases h' : ∃ m, F m = n'
      · rw [ite_eq_left ((hS n').2 h')]
        exact dmap_elem_ne _ _ _ fun ⟨m, _, hm⟩ => hn ⟨m, hm⟩
      · rw [ite_eq_right (fun h => h' ((hS n').1 h))]
        exact dret_0 _ _ (Ne.symm hn')

end uniform

/-! ## Uniform distribution on a finite set -/

section uniform_set

open Classical in
/-- Rocq: `unif_set` (a `gset` becomes a `Finset`). -/
def unif_set (s : Finset α) : Distr α where
  pmf := fun x => if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0
  mass_le_one := by
    rw [SeriesC_finset_indicator]; exact ENNReal.mul_inv_le_one _

theorem unif_set_pmf [DecidableEq α] (s : Finset α) (x : α) :
    unif_set s x = if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  simp only [unif_set, Distr.coe_mk]; congr

/-- Rocq: `unif_set_mass`. -/
theorem unif_set_mass (s : Finset α) (hs : s ≠ ∅) : ∑' x, unif_set s x = 1 := by
  classical
  simp only [unif_set_pmf]
  rw [SeriesC_finset_indicator]
  refine ENNReal.mul_inv_cancel ?_ (ENNReal.natCast_ne_top _)
  exact_mod_cast (Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hs)).ne'

/-- Rocq: `unif_set_pos`. -/
theorem unif_set_pos (s : Finset α) (x : α) : 0 < unif_set s x ↔ s ≠ ∅ ∧ x ∈ s := by
  classical
  rw [unif_set_pmf]
  constructor
  · intro h
    by_cases hx : x ∈ s
    · exact ⟨Finset.ne_empty_of_mem hx, hx⟩
    · simp [hx] at h
  · rintro ⟨-, hx⟩
    rw [ite_eq_left hx]; exact ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)

/-- Rocq: `unif_set_compute`. -/
theorem unif_set_compute (s : Finset α) (x : α) (h : x ∈ s) :
    unif_set s x = (s.card : ℝ≥0∞)⁻¹ := by
  classical rw [unif_set_pmf, ite_eq_left h]

/-- Rocq: `unif_set_compute'`. -/
theorem unif_set_compute' (s : Finset α) (x : α) (h : x ∉ s) : unif_set s x = 0 := by
  classical rw [unif_set_pmf, ite_eq_right h]

end uniform_set

/-! ## Uniform distribution on lists of fixed length -/

section uniform_fin_lists

/-- `∑' v, [length v = p] * c = (N+1)^p * c`. -/
theorem SeriesC_length_indicator (N p : ℕ) (c : ℝ≥0∞) :
    ∑' v : List (Fin (N + 1)), (if v.length = p then c else 0) = ((N + 1) ^ p : ℕ) * c := by
  rw [← (Subtype.val_injective (p := fun v : List (Fin (N + 1)) => v.length = p)).tsum_eq]
  · have : ∀ w : {v : List (Fin (N + 1)) // v.length = p},
        (if w.1.length = p then c else 0) = c := fun w => ite_eq_left w.2
    simp_rw [this]
    show ∑' _ : List.Vector (Fin (N + 1)) p, c = _
    rw [tsum_fintype, Finset.sum_const,
      Finset.card_univ, card_vector, Fintype.card_fin, nsmul_eq_mul]
  · intro v hv
    by_contra h
    exact hv (ite_eq_right fun h' => h ⟨⟨v, h'⟩, rfl⟩)

/-- Rocq: `dunifv`. -/
def dunifv (N p : ℕ) : Distr (List (Fin (N + 1))) where
  pmf := fun x => if x.length = p then (((N + 1) ^ p : ℕ) : ℝ≥0∞)⁻¹ else 0
  mass_le_one := by rw [SeriesC_length_indicator]; exact ENNReal.mul_inv_le_one _

/-- Rocq: `dunifv_pmf`. -/
theorem dunifv_pmf (N p : ℕ) (v : List (Fin (N + 1))) :
    dunifv N p v = if v.length = p then (((N + 1) ^ p : ℕ) : ℝ≥0∞)⁻¹ else 0 := rfl

/-- Rocq: `dunifv_mass`. -/
@[simp] theorem dunifv_mass (N p : ℕ) : ∑' v, dunifv N p v = 1 := by
  simp only [dunifv_pmf]
  rw [SeriesC_length_indicator]
  refine ENNReal.mul_inv_cancel ?_ (ENNReal.natCast_ne_top _)
  exact_mod_cast (pow_pos N.succ_pos p).ne'

/-- Rocq: `dunifv_pos`. -/
theorem dunifv_pos (N p : ℕ) (v : List (Fin (N + 1))) : v.length = p ↔ 0 < dunifv N p v := by
  rw [dunifv_pmf]
  constructor
  · intro h; rw [ite_eq_left h]; exact ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
  · intro h; by_contra h'; rw [ite_eq_right h'] at h; exact lt_irrefl _ h

end uniform_fin_lists

/-! ## Projection out of `Option` -/

section proj_Some

/-- Rocq: `d_proj_Some`. -/
def d_proj_Some : Option α → Distr α
  | some a => dret a
  | none => dzero

/-- Rocq: `d_proj_Some_pos`. -/
theorem d_proj_Some_pos (x : Option α) (y : α) : 0 < d_proj_Some x y ↔ x = some y := by
  cases x with
  | none => simp [d_proj_Some]
  | some a =>
    simp only [d_proj_Some, Option.some.injEq]
    constructor
    · intro h; exact (dret_pos _ _ h).symm
    · rintro rfl; rw [dret_1_1 _ _ rfl]; exact one_pos

/-- Rocq: `d_proj_Some_None`. -/
@[simp] theorem d_proj_Some_None : d_proj_Some (none : Option α) = dzero := rfl

@[simp] theorem d_proj_Some_some (a : α) : d_proj_Some (some a) = dret a := rfl

end proj_Some

section proj_Some_lemmas

/-- Rocq: `d_proj_Some_bind`. -/
theorem d_proj_Some_bind (x : Option α) (f : α → Option β) :
    d_proj_Some (x.bind f) = dbind (fun x' => d_proj_Some (f x')) (d_proj_Some x) := by
  cases x <;> simp

/-- Rocq: `d_proj_Some_fmap`. -/
theorem d_proj_Some_fmap (x : Option α) (f : α → β) :
    d_proj_Some (x.map f) = dbind (fun x' => dret (f x')) (d_proj_Some x) := by
  cases x <;> simp

end proj_Some_lemmas

/-! ## Staircase / layer-integral approximation -/

section staircase

/-- Rocq: `SeriesC_indicator_le`. -/
theorem SeriesC_indicator_le (μ : Distr α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ a, P a → Q a) :
    ∑' a, (if P a then μ a else 0) ≤ ∑' a, (if Q a then μ a else 0) :=
  ENNReal.tsum_le_tsum fun a => by
    by_cases hP : P a
    · simp [hP, h a hP]
    · simp [hP]

/-- Rocq: `threshold_count`:
`threshold_count n x = #{k ∈ {0,…,n-1} | (k+1)/n ≤ x}`.

Deviation: Rocq sums with `sum_f_R0 _ (pred n)`, which has one term (`k = 0`) when `n = 0`,
whereas `Finset.range 0` is empty. The definitions (and those of `step_approx`) therefore agree
with Rocq exactly for `0 < n`, which is the only case any Rocq lemma uses. -/
def threshold_count (n : ℕ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range n, if ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ x then 1 else 0

/-- Rocq: `step_approx`: the `1/n`-grid staircase approximation of `u a` from below,
`step_approx n u a = (1/n) * #{k ∈ {0,…,n−1} | (k+1)/n ≤ u a}`. -/
def step_approx (n : ℕ) (u : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  fun a => (n : ℝ≥0∞)⁻¹ *
    ∑ k ∈ Finset.range n, if ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ u a then 1 else 0

omit [Countable α] in
theorem step_approx_eq (n : ℕ) (u : α → ℝ≥0∞) (a : α) :
    step_approx n u a = (n : ℝ≥0∞)⁻¹ * threshold_count n (u a) := rfl

/-- Rocq: `SeriesC_step_approx`. -/
theorem SeriesC_step_approx (μ : Distr α) (n : ℕ) (u : α → ℝ≥0∞) :
    ∑' a, μ a * step_approx n u a =
      (n : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range n,
        ∑' a, (if ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ u a then μ a else 0) := by
  have : ∀ a, μ a * step_approx n u a = (n : ℝ≥0∞)⁻¹ *
      ∑ k ∈ Finset.range n, (if ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ u a then μ a else 0) := by
    intro a
    rw [step_approx, mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  simp_rw [this, ENNReal.tsum_mul_left]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]

omit [Countable α] in
/-- Rocq: `step_approx_le`. -/
theorem step_approx_le (n : ℕ) (u v : α → ℝ≥0∞) (h : ∀ a, u a ≤ v a) :
    ∀ a, step_approx n u a ≤ step_approx n v a := by
  intro a
  refine mul_le_mul_right (Finset.sum_le_sum fun k _ => ?_) _
  by_cases hu : ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ u a
  · rw [ite_eq_left hu, ite_eq_left (hu.trans (h a))]
  · rw [ite_eq_right hu]; exact zero_le

/-- Rocq: `threshold_bool_iff`. Here `up (n * x) - 1` is `⌊n * x⌋₊`. -/
theorem threshold_bool_iff (n k : ℕ) (x : ℝ≥0∞) (hn : 0 < n) (hx : x ≤ 1) :
    ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ x ↔ k + 1 ≤ ⌊(n : ℝ) * x.toReal⌋₊ := by
  have hx' : x ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hx
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  rw [ENNReal.div_le_iff_le_mul (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n)),
    Nat.le_floor_iff (by positivity),
    ← ENNReal.toReal_le_toReal (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top hx' (ENNReal.natCast_ne_top n)),
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast, mul_comm]

/-- Rocq: `sum_prefix_ones`. -/
theorem sum_prefix_ones (m N : ℕ) (h : m ≤ N + 1) :
    ∑ k ∈ Finset.range (N + 1), (if k + 1 ≤ m then (1 : ℝ≥0∞) else 0) = m := by
  rw [Finset.sum_boole]
  congr 1
  have : (Finset.range (N + 1)).filter (fun k => k + 1 ≤ m) = Finset.range m := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

/-- Rocq: `threshold_count_closed`. Here `up (n * x) - 1` is `⌊n * x⌋₊`. -/
theorem threshold_count_closed (n : ℕ) (x : ℝ≥0∞) (hn : 0 < n) (hx : x ≤ 1) :
    threshold_count n x = (⌊(n : ℝ) * x.toReal⌋₊ : ℝ≥0∞) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [threshold_count]
  simp only [threshold_bool_iff _ _ x hn hx]
  apply sum_prefix_ones
  refine Nat.floor_le_of_le ?_
  have : x.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hx
  have h0 : (0 : ℝ) ≤ ((n' + 1 : ℕ) : ℝ) := by positivity
  calc ((n' + 1 : ℕ) : ℝ) * x.toReal ≤ ((n' + 1 : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left this h0
    _ = _ := by push_cast; ring

/-- Rocq: `threshold_count_sandwich`. -/
theorem threshold_count_sandwich (n : ℕ) (x : ℝ≥0∞) (hn : 0 < n) (hx : x ≤ 1) :
    x - (n : ℝ≥0∞)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ * threshold_count n x ∧
      (n : ℝ≥0∞)⁻¹ * threshold_count n x ≤ x := by
  have hx' : x ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hx
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [threshold_count_closed n x hn hx]
  set m := ⌊(n : ℝ) * x.toReal⌋₊
  have hxr : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hm1 : (m : ℝ) ≤ n * x.toReal := Nat.floor_le (by positivity)
  have hm2 : (n : ℝ) * x.toReal < m + 1 := Nat.lt_floor_add_one _
  have hfin : (n : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne')) (ENNReal.natCast_ne_top _)
  have htr : ((n : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞)).toReal = (n : ℝ)⁻¹ * m := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  constructor
  · rw [tsub_le_iff_right]
    have hfin' : (n : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞) + (n : ℝ≥0∞)⁻¹ ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨hfin, ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne')⟩
    rw [← ENNReal.toReal_le_toReal hx' hfin', ENNReal.toReal_add hfin
      (ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne')), htr, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    rw [← mul_add_one, le_inv_mul_iff₀ hnR]
    exact hm2.le
  · rw [← ENNReal.toReal_le_toReal hfin hx', htr, inv_mul_le_iff₀ hnR]
    exact hm1

omit [Countable α] in
/-- Rocq: `step_approx_bounds_strong`. -/
theorem step_approx_bounds_strong (n : ℕ) (u : α → ℝ≥0∞) (hn : 0 < n) (hu : ∀ a, u a ≤ 1) :
    ∀ a, u a - (n : ℝ≥0∞)⁻¹ ≤ step_approx n u a ∧ step_approx n u a ≤ u a := fun a =>
  threshold_count_sandwich n (u a) hn (hu a)

omit [Countable α] in
/-- Rocq: `step_approx_bounds`. -/
theorem step_approx_bounds (n : ℕ) (u : α → ℝ≥0∞) (hn : 0 < n) (hu : ∀ a, u a ≤ 1) :
    ∀ a, 0 ≤ step_approx n u a ∧ step_approx n u a ≤ u a := fun a =>
  ⟨zero_le, (step_approx_bounds_strong n u hn hu a).2⟩

/-- Rocq: `SeriesC_step_approx_upper`. -/
theorem SeriesC_step_approx_upper (μ : Distr α) (n : ℕ) (u : α → ℝ≥0∞) (hn : 0 < n)
    (hu : ∀ a, u a ≤ 1) : ∑' a, μ a * step_approx n u a ≤ ∑' a, μ a * u a :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_right (step_approx_bounds n u hn hu a).2 _

/-- Rocq: `SeriesC_step_approx_lower`. -/
theorem SeriesC_step_approx_lower (μ : Distr α) (n : ℕ) (u : α → ℝ≥0∞) (hn : 0 < n)
    (hu : ∀ a, u a ≤ 1) :
    ∑' a, μ a * u a - (n : ℝ≥0∞)⁻¹ ≤ ∑' a, μ a * step_approx n u a := by
  rw [tsub_le_iff_right]
  calc ∑' a, μ a * u a ≤ ∑' a, μ a * (step_approx n u a + (n : ℝ≥0∞)⁻¹) :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_right
          (tsub_le_iff_right.1 (step_approx_bounds_strong n u hn hu a).1) _
    _ = ∑' a, μ a * step_approx n u a + (∑' a, μ a) * (n : ℝ≥0∞)⁻¹ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ ∑' a, μ a * step_approx n u a + (n : ℝ≥0∞)⁻¹ := by
        gcongr; exact mul_le_of_le_one_left zero_le μ.mass_le_one

end staircase

/-! ## Tactics

Ports of the Rocq tactics `inv_distr`, `solve_distr`, `solve_distr_mass` and `inv_dzero`.
(The `laplace_rat` cases of the Rocq tactics are dropped together with `laplace_rat`.)
-/

section tactics

open Lean Meta Elab Tactic

/-- If `ty` is `0 < μ x` (or `μ x > 0`) with `μ` headed by one of the constants in `heads`,
return that head constant. -/
meta def distrPosHead? (heads : List Name) (ty : Expr) : MetaM (Option Name) := do
  let ty ← instantiateMVars ty
  let rhs? : Option Expr :=
    match ty.getAppFnArgs with
    | (``LT.lt, #[_, _, _, rhs]) => some rhs
    | (``GT.gt, #[_, _, lhs, _]) => some lhs
    | _ => none
  let some rhs := rhs? | return none
  match rhs.getAppFnArgs with
  | (``Distr.pmf, #[_, _, μ, _]) =>
    match μ.getAppFn.constName? with
    | some c => return if heads.contains c then some c else none
    | none => return none
  | _ => return none

/-- Find the first local hypothesis matching `distrPosHead? heads`. -/
meta def findDistrPosHyp (heads : List Name) : TacticM (Option (FVarId × Name)) :=
  withMainContext do
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      if let some c ← distrPosHead? heads ldecl.type then
        return some (ldecl.fvarId, c)
    return none

/-- If a hypothesis named `n` is still present, give it back the user name `old`. -/
meta def restoreHypName (n old : Name) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  withMainContext do
    if let some ldecl := (← getLCtx).findFromUserName? n then
      let g ← (← getMainGoal).rename ldecl.fvarId old
      replaceMainGoal [g]

/-- One step of `inv_distr`: invert one positivity hypothesis. Returns `false` if there is none. -/
meta def invDistrStep : TacticM Bool := do
  let heads := [``dzero, ``dret, ``dbind, ``dmap, ``d_proj_Some]
  let some (fv, c) ← findDistrPosHyp heads | return false
  let old ← withMainContext do return (← fv.getDecl).userName
  let n ← mkFreshUserName `h
  let g ← (← getMainGoal).rename fv n
  replaceMainGoal [g]
  let h := mkIdent n
  if c == ``dzero then
    evalTactic (← `(tactic| exact absurd $h (dzero_supp_empty _)))
  else if c == ``dret then
    evalTactic (← `(tactic| replace $h:ident := dret_pos _ _ $h))
    evalTactic (← `(tactic| try subst $h:ident))
    restoreHypName n old
  else if c == ``dbind then
    evalTactic (← `(tactic| obtain ⟨_, _, _⟩ := (dbind_pos _ _ _).1 $h))
    evalTactic (← `(tactic| clear $h:ident))
  else if c == ``dmap then
    let e := mkIdent (← mkFreshUserName `e)
    evalTactic (← `(tactic| obtain ⟨_, $e:ident, _⟩ := (dmap_pos _ _ _).1 $h))
    evalTactic (← `(tactic| clear $h:ident))
    evalTactic (← `(tactic| try subst $e:ident))
  else if c == ``d_proj_Some then
    evalTactic (← `(tactic| replace $h:ident := (d_proj_Some_pos _ _).1 $h))
    evalTactic (← `(tactic| try subst $h:ident))
    restoreHypName n old
  return true

/-- Rocq: `inv_distr`. Repeatedly inverts hypotheses `0 < dzero x`, `0 < dret a x`,
`0 < dbind f μ x`, `0 < dmap f μ x` and `0 < d_proj_Some o x` (also in `_ > 0` form),
using `dzero_supp_empty`, `dret_pos`, `dbind_pos`, `dmap_pos` and `d_proj_Some_pos`,
introducing the witnesses and substituting equations where possible. -/
elab "inv_distr" : tactic => do
  let mut fuel := 1000
  while fuel > 0 do
    fuel := fuel - 1
    if (← getGoals).isEmpty then return
    unless ← invDistrStep do return

/-- Rocq: `solve_distr`. Repeatedly reduces goals `0 < dret a x`, `dret x x = 1`,
`0 < dmap f μ x`, `0 < dbind f μ x`, `0 < dunifP N n`, `0 < dunifv N p v`,
`0 < unif_set s x` and `0 < d_proj_Some o x` (also in `_ > 0` form). For `dbind` the
intermediate witness is left as a metavariable goal (Rocq's `eexists`). -/
macro "solve_distr" : tactic => `(tactic| repeat (first
  | exact (dret_pos_iff _ _).2 rfl
  | exact dret_1_1 _ _ rfl
  | exact (dmap_pos _ _ _).2 ⟨_, rfl, by assumption⟩
  | refine (dmap_pos _ _ _).2 ⟨_, rfl, ?_⟩
  | refine (dbind_pos _ _ _).2 ⟨?_, ?_, ?_⟩
  | exact dunifP_pos _ _
  | refine (dunifv_pos _ _ _).1 ?_
  | refine (unif_set_pos _ _).2 ?_
  | refine (d_proj_Some_pos _ _).2 ?_))

/-- Rocq: `solve_distr_mass`: goals `∑' a, μ a = 1` (or `0 < ∑' a, dret x a`) for the basic
distributions. -/
macro "solve_distr_mass" : tactic => `(tactic| first
  | exact dret_mass _
  | (rw [dret_mass]; exact one_pos)
  | (rw [dmap_mass]; done)
  | (rw [dmap_mass]; assumption)
  | exact dunif_mass _ (by assumption)
  | exact dunif_mass _ (by simp)
  | exact dunifP_mass _
  | exact dunifv_mass _ _
  | exact unif_set_mass _ (by assumption))

/-- One step of `inv_dzero`. Returns `false` if no hypothesis applies. -/
meta def invDzeroStep : TacticM Bool := withMainContext do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let (``Eq, #[_, lhs, rhs]) := ty.getAppFnArgs | continue
    unless rhs.getAppFn.constName? == some ``dzero do continue
    let some c := lhs.getAppFn.constName? | continue
    unless [``dret, ``dunifP, ``dmap].contains c do continue
    let n ← mkFreshUserName `h
    let g ← (← getMainGoal).rename ldecl.fvarId n
    replaceMainGoal [g]
    let h := mkIdent n
    if c == ``dret then
      evalTactic (← `(tactic| exact absurd $h (dret_not_dzero _)))
    else if c == ``dunifP then
      evalTactic (← `(tactic| exact absurd $h (dunifP_not_dzero _)))
    else
      evalTactic (← `(tactic| replace $h:ident := dmap_dzero_inv _ _ $h))
      restoreHypName n ldecl.userName
    return true
  return false

/-- Rocq: `inv_dzero`: uses hypotheses `dret _ = dzero` / `dunifP _ = dzero` (contradiction)
and `dmap f μ = dzero` (replaced by `μ = dzero`). -/
elab "inv_dzero" : tactic => do
  let mut fuel := 1000
  while fuel > 0 do
    fuel := fuel - 1
    if (← getGoals).isEmpty then return
    unless ← invDzeroStep do return

end tactics

end Prob
