module

public import Metrology.Prob.Couplings
public import Metrology.Prob.GradedPredicateLifting

/-!
# Approximate couplings

Ported from clutch/theories/prob/couplings_app.v

`ARcoupl μ₁ μ₂ S ε` states that for every pair of `[0,1]`-valued test functions `f`, `g` with
`S a b → f a ≤ g b`, the expectation of `f` under `μ₁` exceeds the expectation of `g` under `μ₂`
by at most `ε`.

Compared with the Rocq development:
* test functions are `α → ℝ≥0∞` bounded by `1` (the lower bound `0 ≤ f a` is automatic);
* errors `ε` are `ℝ≥0∞`, so all hypotheses `0 <= ε` are dropped;
* summability side conditions, and the boundedness hypotheses `∃ n, ∀ a, 0 <= E2 a <= n` of
  `ARcoupl_dbind_adv_lhs'` / `ARcoupl_dbind_adv_rhs'`, are dropped;
* Rocq's `(M-N)/M` is written `((M : ℝ≥0∞) - N) / M` (truncated subtraction, which agrees with
  Rocq since `N ≤ M`), and `1/N` is `1 / (N : ℝ≥0∞)`;
* `Inj`/`Bij` instances become `Function.Injective`/`Function.Bijective` hypotheses;
* `ARcoupl_sets` decides its predicates classically (as Rocq does with `make_decision`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Prob

variable {α β α' β' : Type*} [Countable α] [Countable β] [Countable α'] [Countable β']

/-! ## Definition -/

section couplings

/-- Rocq: `ARcoupl`. -/
def ARcoupl (μ1 : Distr α) (μ2 : Distr β) (S : α → β → Prop) (ε : ℝ≥0∞) : Prop :=
  ∀ (f : α → ℝ≥0∞) (g : β → ℝ≥0∞),
    (∀ a, f a ≤ 1) →
    (∀ b, g b ≤ 1) →
    (∀ a b, S a b → f a ≤ g b) →
    ∑' a, μ1 a * f a ≤ ∑' b, μ2 b * g b + ε

end couplings

/-! ## Helpers (not in Rocq) -/

/-- The expectation of a `[0,1]`-valued function is bounded by the mass. -/
theorem SeriesC_mul_le_mass (μ : Distr α) (f : α → ℝ≥0∞) (hf : ∀ a, f a ≤ 1) :
    ∑' a, μ a * f a ≤ ∑' a, μ a :=
  ENNReal.tsum_le_tsum fun a => mul_le_of_le_one_right' (hf a)

/-- The expectation of a `[0,1]`-valued function is at most `1`. -/
theorem SeriesC_mul_le_one (μ : Distr α) (f : α → ℝ≥0∞) (hf : ∀ a, f a ≤ 1) :
    ∑' a, μ a * f a ≤ 1 :=
  (SeriesC_mul_le_mass μ f hf).trans μ.mass_le_one

/-- `Expval_dret` written as a series. -/
theorem SeriesC_dret_mul (a : α) (f : α → ℝ≥0∞) : ∑' x, dret a x * f x = f a :=
  Expval_dret f a

/-! ## Basic theory -/

section couplings_theory

/-- Rocq: `ARcoupl_mono`. -/
theorem ARcoupl_mono (μ1 μ1' : Distr α') (μ2 μ2' : Distr β') (R R' : α' → β' → Prop)
    (ε ε' : ℝ≥0∞) (Hμ1 : ∀ a, μ1 a = μ1' a) (Hμ2 : ∀ b, μ2 b = μ2' b)
    (HR : ∀ x y, R x y → R' x y) (Hε : ε ≤ ε') (Hcoupl : ARcoupl μ1 μ2 R ε) :
    ARcoupl μ1' μ2' R' ε' := by
  obtain rfl := distr_ext Hμ1
  obtain rfl := distr_ext Hμ2
  intro f g Hf Hg Hfg
  calc _ ≤ _ := Hcoupl f g Hf Hg fun a b h => Hfg a b (HR a b h)
    _ ≤ _ := by gcongr

/-- Rocq: `ARcoupl_1`. -/
theorem ARcoupl_1 (μ1 : Distr α') (μ2 : Distr β') (R : α' → β' → Prop) (ε : ℝ≥0∞)
    (Hε : 1 ≤ ε) : ARcoupl μ1 μ2 R ε := by
  intro f g Hf _ _
  calc ∑' a, μ1 a * f a ≤ 1 := SeriesC_mul_le_one μ1 f Hf
    _ ≤ ε := Hε
    _ ≤ _ := le_add_self

/-- Rocq: `ARcoupl_mon_grading`. -/
theorem ARcoupl_mon_grading (μ1 : Distr α') (μ2 : Distr β') (R : α' → β' → Prop)
    (ε1 ε2 : ℝ≥0∞) (Hleq : ε1 ≤ ε2) (HR : ARcoupl μ1 μ2 R ε1) : ARcoupl μ1 μ2 R ε2 := by
  intro f g Hf Hg Hfg
  calc _ ≤ _ := HR f g Hf Hg Hfg
    _ ≤ _ := by gcongr

/-- Capping the error at `1` preserves approximate couplings (helper). -/
theorem ARcoupl_min_one (μ1 : Distr α') (μ2 : Distr β') (R : α' → β' → Prop) (ε : ℝ≥0∞)
    (H : ARcoupl μ1 μ2 R ε) : ARcoupl μ1 μ2 R (min 1 ε) := by
  rcases le_total 1 ε with h | h
  · rw [min_eq_left h]; exact ARcoupl_1 _ _ _ _ le_rfl
  · rwa [min_eq_right h]

/-- Rocq: `ARcoupl_dret` (the hypothesis `0 <= r` is dropped). -/
theorem ARcoupl_dret (a : α) (b : β) (R : α → β → Prop) (r : ℝ≥0∞) (HR : R a b) :
    ARcoupl (dret a) (dret b) R r := by
  intro f g _ _ Hfg
  rw [SeriesC_dret_mul, SeriesC_dret_mul]
  exact (Hfg a b HR).trans le_self_add

/-- Rocq: `ARcoupl_ret_inv`. -/
theorem ARcoupl_ret_inv (a : α) (b : β) (ψ : α → β → Prop) (ε : ℝ≥0∞) (hε : ε < 1)
    (H : ARcoupl (dret a) (dret b) ψ ε) : ψ a b := by
  classical
  by_contra hψ
  have := H (fun x => if x = a then 1 else 0) (fun y => if y = b then 0 else 1)
    (fun x => by split_ifs <;> simp) (fun y => by split_ifs <;> simp)
    (fun x y hxy => by
      by_cases hx : x = a
      · subst hx
        by_cases hy : y = b
        · subst hy; exact absurd hxy hψ
        · simp [hy]
      · simp [hx])
  rw [SeriesC_dret_mul, SeriesC_dret_mul] at this
  simp only [ite_true, zero_add] at this
  exact absurd hε (not_lt.2 this)

/-- Rocq: `ARcoupl_dbind_adv_kanto_plain` (the error may depend on both sides). -/
theorem ARcoupl_dbind_adv_kanto_plain (f : α → Distr α') (g : β → Distr β')
    (μ1 : Distr α) (μ2 : Distr β) (S' : α' → β' → Prop) (ε2 : ℝ≥0∞) (E2 : α → β → ℝ≥0∞)
    (Hε2 : ∀ (h1 : α → ℝ≥0∞) (h2 : β → ℝ≥0∞),
      (∀ a, h1 a ≤ 1) → (∀ b, h2 b ≤ 1) → (∀ a b, h1 a ≤ h2 b + E2 a b) →
      ∑' a, μ1 a * h1 a ≤ ∑' b, μ2 b * h2 b + ε2)
    (Hcoup_fg : ∀ a b, ARcoupl (f a) (g b) S' (E2 a b)) :
    ARcoupl (dbind f μ1) (dbind g μ2) S' ε2 := by
  intro h1 h2 Hh1 Hh2 Hh12
  have e1 := Expval_dbind μ1 f h1
  have e2 := Expval_dbind μ2 g h2
  unfold Expval at e1 e2
  rw [e1, e2]
  exact Hε2 _ _ (fun a => SeriesC_mul_le_one (f a) h1 Hh1)
    (fun b => SeriesC_mul_le_one (g b) h2 Hh2)
    (fun a b => Hcoup_fg a b h1 h2 Hh1 Hh2 Hh12)

/-- Rocq: `ARcoupl_dbind_adv_kanto_full`. -/
theorem ARcoupl_dbind_adv_kanto_full (f : α → Distr α') (g : β → Distr β')
    (μ1 : Distr α) (μ2 : Distr β) (S : α → β → Prop) (S' : α' → β' → Prop)
    (ε1 ε2 : ℝ≥0∞) (E2 : α → β → ℝ≥0∞)
    (Hε2 : ∀ (h1 : α → ℝ≥0∞) (h2 : β → ℝ≥0∞),
      (∀ a, h1 a ≤ 1) → (∀ b, h2 b ≤ 1) → (∀ a b, S a b → h1 a ≤ h2 b + E2 a b) →
      ∑' a, μ1 a * h1 a ≤ ∑' b, μ2 b * h2 b + ε2)
    (_HcoupR : ARcoupl μ1 μ2 S ε1)
    (Hcoup_fg : ∀ a b, S a b → ARcoupl (f a) (g b) S' (E2 a b)) :
    ARcoupl (dbind f μ1) (dbind g μ2) S' ε2 := by
  classical
  refine ARcoupl_dbind_adv_kanto_plain f g μ1 μ2 S' ε2
    (fun a b => if S a b then E2 a b else 1) ?_ ?_
  · intro h1 h2 Hh1 Hh2 Hh12
    exact Hε2 h1 h2 Hh1 Hh2 fun a b hS => by simpa [hS] using Hh12 a b
  · intro a b
    by_cases hS : S a b
    · simpa [hS] using Hcoup_fg a b hS
    · simpa [hS] using ARcoupl_1 (f a) (g b) S' 1 le_rfl

/-- Rocq: `ARcoupl_adv_kanto_invert`. -/
theorem ARcoupl_adv_kanto_invert (μ1 : Distr α) (μ2 : Distr β) (S : α → β → Prop)
    (ε1 ε2 : ℝ≥0∞) (Hcpl : ARcoupl μ1 μ2 S ε1) :
    ∀ (h1 : α → ℝ≥0∞) (h2 : β → ℝ≥0∞),
      (∀ a, h1 a ≤ 1) → (∀ b, h2 b ≤ 1) → (∀ a b, S a b → h1 a ≤ h2 b + ε2) →
      Expval μ1 h1 ≤ Expval μ2 h2 + (ε1 + ε2) := by
  intro h1 h2 Hh1 _ Hh12
  have key := Hcpl h1 (fun b => min 1 (h2 b + ε2)) Hh1 (fun _ => min_le_left _ _)
    (fun a b hS => le_min (Hh1 a) (Hh12 a b hS))
  unfold Expval
  calc _ ≤ _ := key
    _ ≤ ∑' b, μ2 b * h2 b + ε2 + ε1 := by
      gcongr
      calc ∑' b, μ2 b * min 1 (h2 b + ε2) ≤ ∑' b, (μ2 b * h2 b + μ2 b * ε2) :=
            ENNReal.tsum_le_tsum fun b => by rw [← mul_add]; gcongr; exact min_le_right _ _
        _ = ∑' b, μ2 b * h2 b + (∑' b, μ2 b) * ε2 := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        _ ≤ _ := by gcongr; exact mul_le_of_le_one_left zero_le μ2.mass_le_one
    _ = _ := by ring

/-- Rocq: `ARcoupl_dbind_adv_lhs` (the error depends on the left-hand side). -/
theorem ARcoupl_dbind_adv_lhs (f : α → Distr α') (g : β → Distr β')
    (μ1 : Distr α) (μ2 : Distr β) (S : α → β → Prop) (S' : α' → β' → Prop)
    (ε1 ε2 : ℝ≥0∞) (E2 : α → ℝ≥0∞) (_HE2 : ∀ a, E2 a ≤ 1)
    (Hε2 : ∑' a, μ1 a * E2 a = ε2)
    (Hcoup_fg : ∀ a b, S a b → ARcoupl (f a) (g b) S' (E2 a))
    (Hcoup_R : ARcoupl μ1 μ2 S ε1) :
    ARcoupl (dbind f μ1) (dbind g μ2) S' (ε1 + ε2) := by
  classical
  refine ARcoupl_dbind_adv_kanto_plain f g μ1 μ2 S' _
    (fun a b => if S a b then E2 a else 1) ?_ ?_
  · intro h1 h2 Hh1 Hh2 Hh12
    rw [← Hε2]
    have key := Hcoup_R (fun a => h1 a - E2 a) h2 (fun a => tsub_le_self.trans (Hh1 a)) Hh2
      (fun a b hS => by
        have := Hh12 a b
        simp only [hS, ite_true] at this
        exact tsub_le_iff_right.2 this)
    calc ∑' a, μ1 a * h1 a ≤ ∑' a, (μ1 a * (h1 a - E2 a) + μ1 a * E2 a) :=
          ENNReal.tsum_le_tsum fun a => by rw [← mul_add]; gcongr; exact le_tsub_add
      _ = ∑' a, μ1 a * (h1 a - E2 a) + ∑' a, μ1 a * E2 a := ENNReal.tsum_add
      _ ≤ ∑' b, μ2 b * h2 b + ε1 + ∑' a, μ1 a * E2 a := by gcongr
      _ = _ := by ring
  · intro a b
    by_cases hS : S a b
    · simpa [hS] using Hcoup_fg a b hS
    · simpa [hS] using ARcoupl_1 (f a) (g b) S' 1 le_rfl

/-- Rocq: `ARcoupl_dbind_adv_lhs'` (the boundedness hypothesis on `E2` is dropped). -/
theorem ARcoupl_dbind_adv_lhs' (E2 : α → ℝ≥0∞) (f : α → Distr α') (g : β → Distr β')
    (μ1 : Distr α) (μ2 : Distr β) (S : α → β → Prop) (S' : α' → β' → Prop)
    (ε1 ε2 : ℝ≥0∞) (Hsum : ∑' a, μ1 a * E2 a ≤ ε2)
    (Hfg : ∀ a b, S a b → ARcoupl (f a) (g b) S' (E2 a)) (Hcoupl : ARcoupl μ1 μ2 S ε1) :
    ARcoupl (dbind f μ1) (dbind g μ2) S' (ε1 + ε2) := by
  refine ARcoupl_mon_grading _ _ _ (ε1 + ∑' a, μ1 a * min 1 (E2 a)) _ ?_ ?_
  · gcongr
    exact (ENNReal.tsum_le_tsum fun a => by gcongr; exact min_le_right _ _).trans Hsum
  · exact ARcoupl_dbind_adv_lhs f g μ1 μ2 S S' ε1 _ (fun a => min 1 (E2 a))
      (fun _ => min_le_left _ _) rfl
      (fun a b hS => ARcoupl_min_one _ _ _ _ (Hfg a b hS)) Hcoupl

/-- Rocq: `ARcoupl_dbind_adv_rhs` (the error depends on the right-hand side). -/
theorem ARcoupl_dbind_adv_rhs (f : α → Distr α') (g : β → Distr β')
    (μ1 : Distr α) (μ2 : Distr β) (S : α → β → Prop) (S' : α' → β' → Prop)
    (ε1 ε2 : ℝ≥0∞) (E2 : β → ℝ≥0∞) (_HE2 : ∀ b, E2 b ≤ 1)
    (Hε2 : ∑' b, μ2 b * E2 b = ε2)
    (Hcoup_fg : ∀ a b, S a b → ARcoupl (f a) (g b) S' (E2 b))
    (Hcoup_R : ARcoupl μ1 μ2 S ε1) :
    ARcoupl (dbind f μ1) (dbind g μ2) S' (ε1 + ε2) := by
  classical
  refine ARcoupl_dbind_adv_kanto_plain f g μ1 μ2 S' _
    (fun a b => if S a b then E2 b else 1) ?_ ?_
  · intro h1 h2 Hh1 _ Hh12
    rw [← Hε2]
    have key := Hcoup_R h1 (fun b => min 1 (h2 b + E2 b)) Hh1 (fun _ => min_le_left _ _)
      (fun a b hS => le_min (Hh1 a) (by simpa [hS] using Hh12 a b))
    calc _ ≤ _ := key
      _ ≤ ∑' b, (μ2 b * h2 b + μ2 b * E2 b) + ε1 := by
          gcongr ?_ + _
          exact ENNReal.tsum_le_tsum fun b => by rw [← mul_add]; gcongr; exact min_le_right _ _
      _ = _ := by rw [ENNReal.tsum_add]; ring
  · intro a b
    by_cases hS : S a b
    · simpa [hS] using Hcoup_fg a b hS
    · simpa [hS] using ARcoupl_1 (f a) (g b) S' 1 le_rfl

/-- Rocq: `ARcoupl_dbind_adv_rhs'` (the boundedness hypothesis on `E2` is dropped). -/
theorem ARcoupl_dbind_adv_rhs' (E2 : β → ℝ≥0∞) (f : α → Distr α') (g : β → Distr β')
    (μ1 : Distr α) (μ2 : Distr β) (S : α → β → Prop) (S' : α' → β' → Prop)
    (ε1 ε2 : ℝ≥0∞) (Hsum : ∑' b, μ2 b * E2 b ≤ ε2)
    (Hfg : ∀ a b, S a b → ARcoupl (f a) (g b) S' (E2 b)) (Hcoupl : ARcoupl μ1 μ2 S ε1) :
    ARcoupl (dbind f μ1) (dbind g μ2) S' (ε1 + ε2) := by
  refine ARcoupl_mon_grading _ _ _ (ε1 + ∑' b, μ2 b * min 1 (E2 b)) _ ?_ ?_
  · gcongr
    exact (ENNReal.tsum_le_tsum fun b => by gcongr; exact min_le_right _ _).trans Hsum
  · exact ARcoupl_dbind_adv_rhs f g μ1 μ2 S S' ε1 _ (fun b => min 1 (E2 b))
      (fun _ => min_le_left _ _) rfl
      (fun a b hS => ARcoupl_min_one _ _ _ _ (Hfg a b hS)) Hcoupl

/-- Rocq: `ARcoupl_dbind` (the hypotheses `0 <= ε1`, `0 <= ε2` are dropped). -/
theorem ARcoupl_dbind (f : α → Distr α') (g : β → Distr β')
    (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) (S : α' → β' → Prop) (ε1 ε2 : ℝ≥0∞)
    (Hcoup_fg : ∀ a b, R a b → ARcoupl (f a) (g b) S ε2) (Hcoup_R : ARcoupl μ1 μ2 R ε1) :
    ARcoupl (dbind f μ1) (dbind g μ2) S (ε1 + ε2) := by
  refine ARcoupl_mon_grading _ _ _ (ε1 + ∑' b, μ2 b * min ε2 1) _ ?_ ?_
  · gcongr
    rw [ENNReal.tsum_mul_right]
    calc (∑' b, μ2 b) * min ε2 1 ≤ 1 * min ε2 1 := by gcongr; exact μ2.mass_le_one
      _ ≤ ε2 := by rw [one_mul]; exact min_le_left _ _
  · exact ARcoupl_dbind_adv_rhs f g μ1 μ2 R S ε1 _ (fun _ => min ε2 1)
      (fun _ => min_le_right _ _) rfl
      (fun a b h => by rw [min_comm]; exact ARcoupl_min_one _ _ _ _ (Hcoup_fg a b h)) Hcoup_R

/-- Rocq: `ARcoupl_dbind'`. -/
theorem ARcoupl_dbind' (ε1 ε2 ε : ℝ≥0∞) (f : α → Distr α') (g : β → Distr β')
    (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) (S : α' → β' → Prop)
    (Hε : ε = ε1 + ε2) (Hcoup_fg : ∀ a b, R a b → ARcoupl (f a) (g b) S ε2)
    (Hcoup_R : ARcoupl μ1 μ2 R ε1) : ARcoupl (dbind f μ1) (dbind g μ2) S ε := by
  subst Hε; exact ARcoupl_dbind f g μ1 μ2 R S ε1 ε2 Hcoup_fg Hcoup_R

/-- Rocq: `ARcoupl_mass_leq`. -/
theorem ARcoupl_mass_leq (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) (ε : ℝ≥0∞)
    (Hcoupl : ARcoupl μ1 μ2 R ε) : ∑' a, μ1 a ≤ ∑' b, μ2 b + ε := by
  simpa using Hcoupl (fun _ => 1) (fun _ => 1) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ _ _ => le_rfl)

/-- Rocq: `ARcoupl_eq`. -/
theorem ARcoupl_eq (μ1 : Distr α) : ARcoupl μ1 μ1 (· = ·) 0 := by
  intro f g _ _ Hfg
  rw [add_zero]
  exact ENNReal.tsum_le_tsum fun a => by gcongr; exact Hfg a a rfl

/-- Rocq: `ARcoupl_eq_elim`. -/
theorem ARcoupl_eq_elim (μ1 μ2 : Distr α) (ε : ℝ≥0∞) (Hcoupl : ARcoupl μ1 μ2 (· = ·) ε) :
    ∀ a, μ1 a ≤ μ2 a + ε := by
  classical
  intro a
  have := Hcoupl (fun x => if x = a then 1 else 0) (fun x => if x = a then 1 else 0)
    (fun x => by split_ifs <;> simp) (fun x => by split_ifs <;> simp)
    (fun _ _ h => h ▸ le_rfl)
  simpa [mul_ite] using this

/-- Rocq: `ARcoupl_eq_elim_tv`. -/
theorem ARcoupl_eq_elim_tv (μ1 μ2 : Distr α) (ε : ℝ≥0∞) (Hcoupl : ARcoupl μ1 μ2 (· = ·) ε)
    (P : α → Prop) [DecidablePred P] :
    ∑' a, (if P a then μ1 a else 0) ≤ ∑' a, (if P a then μ2 a else 0) + ε := by
  have := Hcoupl (fun x => if P x then 1 else 0) (fun x => if P x then 1 else 0)
    (fun x => by split_ifs <;> simp) (fun x => by split_ifs <;> simp)
    (fun _ _ h => h ▸ le_rfl)
  simpa [mul_ite] using this

end couplings_theory

/-! ## Further lemmas -/

section ARcoupl

variable (μ1 : Distr α) (μ2 : Distr β)

/-- Rocq: `ARcoupl_trivial`. -/
theorem ARcoupl_trivial (Hμ1 : ∑' a, μ1 a = 1) (Hμ2 : ∑' b, μ2 b = 1) :
    ARcoupl μ1 μ2 (fun _ _ => True) 0 := by
  intro f g _ _ Hfg
  have hs : ∀ b, (⨆ a, f a) ≤ g b := fun b => iSup_le fun a => Hfg a b trivial
  calc ∑' a, μ1 a * f a ≤ ∑' a, μ1 a * (⨆ a, f a) :=
        ENNReal.tsum_le_tsum fun a => by gcongr; exact le_iSup f a
    _ = ⨆ a, f a := by rw [ENNReal.tsum_mul_right, Hμ1, one_mul]
    _ = ∑' b, μ2 b * (⨆ a, f a) := by rw [ENNReal.tsum_mul_right, Hμ2, one_mul]
    _ ≤ ∑' b, μ2 b * g b := ENNReal.tsum_le_tsum fun b => by gcongr; exact hs b
    _ = _ := (add_zero _).symm

/-- Rocq: `ARcoupl_pos_R`. -/
theorem ARcoupl_pos_R (R : α → β → Prop) (ε : ℝ≥0∞) (Hμ1μ2 : ARcoupl μ1 μ2 R ε) :
    ARcoupl μ1 μ2 (fun a b => R a b ∧ 0 < μ1 a ∧ 0 < μ2 b) ε := by
  classical
  intro f g Hf Hg Hfg
  have e1 : ∑' a, μ1 a * f a = ∑' a, μ1 a * (if 0 < μ1 a then f a else 0) :=
    tsum_congr fun a => by
      by_cases h : 0 < μ1 a
      · simp [h]
      · simp [pmf_eq_0_not_gt_0 μ1 a h]
  have e2 : ∑' b, μ2 b * g b = ∑' b, μ2 b * (if 0 < μ2 b then g b else 1) :=
    tsum_congr fun b => by
      by_cases h : 0 < μ2 b
      · simp [h]
      · simp [pmf_eq_0_not_gt_0 μ2 b h]
  rw [e1, e2]
  refine Hμ1μ2 _ _ (fun a => ?_) (fun b => ?_) (fun a b hR => ?_)
  · split_ifs
    · exact Hf a
    · exact zero_le
  · split_ifs
    · exact Hg b
    · exact le_rfl
  · by_cases h1 : 0 < μ1 a
    · by_cases h2 : 0 < μ2 b
      · simpa [h1, h2] using Hfg a b ⟨hR, h1, h2⟩
      · simpa [h1, h2] using Hf a
    · simp [h1]

end ARcoupl

/-! ## Characterisation through events -/

section ARcoupl_sets

open Classical in
/-- Rocq: `ARcoupl_sets`. -/
def ARcoupl_sets (μ1 : Distr α) (μ2 : Distr β) (P : α → β → Prop) (ε : ℝ≥0∞) : Prop :=
  ∀ (P1 : α → Prop) (P2 : β → Prop),
    (∀ a b, P a b → P1 a → P2 b) →
    prob μ1 (fun a => decide (P1 a)) ≤ prob μ2 (fun b => decide (P2 b)) + ε

/-- Rocq: `exp_val_from_interval`. -/
theorem exp_val_from_interval (μ1 : Distr α) (μ2 : Distr β) (f : α → ℝ≥0∞) (g : β → ℝ≥0∞)
    (ε : ℝ≥0∞) (Hf : ∀ a, f a ≤ 1) (Hg : ∀ b, g b ≤ 1)
    (Hr : ∀ r : ℝ≥0∞, r ≤ 1 →
      prob μ1 (fun a => decide (r ≤ f a)) ≤ prob μ2 (fun b => decide (r ≤ g b)) + ε) :
    ∑' a, μ1 a * f a ≤ ∑' b, μ2 b * g b + ε := by
  have Hcore : ∀ n : ℕ, 0 < n →
      ∑' a, μ1 a * f a ≤ ∑' b, μ2 b * g b + ε + (n : ℝ≥0∞)⁻¹ := by
    intro n hn
    have h1 := SeriesC_step_approx_lower μ1 n f hn Hf
    rw [tsub_le_iff_right] at h1
    refine h1.trans ?_
    gcongr ?_ + _
    have hup : ∑' b, μ2 b * step_approx n g b + ε ≤ ∑' b, μ2 b * g b + ε := by
      gcongr ?_ + _; exact SeriesC_step_approx_upper μ2 n g hn Hg
    refine le_trans ?_ hup
    rw [SeriesC_step_approx, SeriesC_step_approx]
    have hk : ∀ k ∈ Finset.range n,
        ∑' a, (if ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ f a then μ1 a else 0) ≤
          ∑' b, (if ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ g b then μ2 b else 0) + ε := by
      intro k hk
      have hr : ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ 1 := by
        refine ENNReal.div_le_of_le_mul ?_
        rw [one_mul]
        exact_mod_cast Finset.mem_range.1 hk
      simpa [prob] using Hr _ hr
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
    calc (n : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range n,
          ∑' a, (if ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ f a then μ1 a else 0)
        ≤ (n : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range n,
          (∑' b, (if ((k + 1 : ℕ) : ℝ≥0∞) / n ≤ g b then μ2 b else 0) + ε) := by
          gcongr with k hk'
          exact hk k hk'
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_add,
            ← mul_assoc, ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n), one_mul]
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (δ : ℝ≥0∞)) (by exact_mod_cast hδ.ne')
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hn
    · exact h
  exact (Hcore n hnpos).trans (by gcongr)

/-- Rocq: `equiv_ARcoupl_sets_1`. -/
theorem equiv_ARcoupl_sets_1 (μ1 : Distr α) (μ2 : Distr β) (P : α → β → Prop) (ε : ℝ≥0∞)
    (Hcoupl : ARcoupl_sets μ1 μ2 P ε) : ARcoupl μ1 μ2 P ε := by
  intro f g Hf Hg Hfg
  refine exp_val_from_interval μ1 μ2 f g ε Hf Hg fun r _ => ?_
  have := Hcoupl (fun a => r ≤ f a) (fun b => r ≤ g b)
    (fun a b h hr => hr.trans (Hfg a b h))
  convert this using 4
  congr!

/-- Rocq: `equiv_ARcoupl_sets_2`. -/
theorem equiv_ARcoupl_sets_2 (μ1 : Distr α) (μ2 : Distr β) (P : α → β → Prop) (ε : ℝ≥0∞)
    (Hcoupl : ARcoupl μ1 μ2 P ε) : ARcoupl_sets μ1 μ2 P ε := by
  classical
  intro P1 P2 HP12
  have := Hcoupl (fun a => if P1 a then 1 else 0) (fun b => if P2 b then 1 else 0)
    (fun a => by split_ifs <;> simp) (fun b => by split_ifs <;> simp)
    (fun a b hab => by
      by_cases h1 : P1 a
      · simp [h1, HP12 a b hab h1]
      · simp [h1])
  unfold prob
  convert this using 3 <;> simp [mul_ite]

/-- Rocq: `equiv_ARcoupl_sets`. -/
theorem equiv_ARcoupl_sets (μ1 : Distr α) (μ2 : Distr β) (P : α → β → Prop) (ε : ℝ≥0∞) :
    ARcoupl_sets μ1 μ2 P ε ↔ ARcoupl μ1 μ2 P ε :=
  ⟨equiv_ARcoupl_sets_1 μ1 μ2 P ε, equiv_ARcoupl_sets_2 μ1 μ2 P ε⟩

end ARcoupl_sets

/-! ## Zero distributions, maps and transitivity -/

/-- Rocq: `ARcoupl_dzero_dzero`. -/
theorem ARcoupl_dzero_dzero (R : α → β → Prop) :
    ARcoupl (dzero : Distr α) (dzero : Distr β) R 0 := by
  intro f g _ _ _
  simp

/-- Rocq: `ARcoupl_dzero_r_inv`. -/
theorem ARcoupl_dzero_r_inv (μ1 : Distr α) (R : α → β → Prop)
    (Hz : ARcoupl μ1 (dzero : Distr β) R 0) : μ1 = dzero :=
  SeriesC_zero_dzero μ1 (by simpa using ARcoupl_mass_leq _ _ _ _ Hz)

/-- Rocq: `ARcoupl_dzero` (the hypothesis `0 <= ε` is dropped). -/
theorem ARcoupl_dzero (μ : Distr β) (R : α → β → Prop) (ε : ℝ≥0∞) :
    ARcoupl (dzero : Distr α) μ R ε := by
  intro f g _ _ _
  simp

/-- Rocq: `ARcoupl_map` (the hypothesis `0 <= ε` is dropped). -/
theorem ARcoupl_map (f : α → α') (g : β → β') (μ1 : Distr α) (μ2 : Distr β)
    (R : α' → β' → Prop) (ε : ℝ≥0∞) (Hcoupl : ARcoupl μ1 μ2 (fun a a' => R (f a) (g a')) ε) :
    ARcoupl (dmap f μ1) (dmap g μ2) R ε := by
  have := ARcoupl_dbind (fun a => dret (f a)) (fun b => dret (g b)) μ1 μ2 _ R ε 0
    (fun a b h => ARcoupl_dret _ _ _ _ h) Hcoupl
  rwa [add_zero] at this

/-- Rocq: `ARcoupl_map_inv` (the hypothesis `0 <= ε` is dropped). -/
theorem ARcoupl_map_inv (f : α → α') (g : β → β') (μ1 : Distr α) (μ2 : Distr β)
    (R : α' → β' → Prop) (ε : ℝ≥0∞) (Hcoupl : ARcoupl (dmap f μ1) (dmap g μ2) R ε) :
    ARcoupl μ1 μ2 (fun a a' => R (f a) (g a')) ε := by
  classical
  apply equiv_ARcoupl_sets_1
  have H := equiv_ARcoupl_sets_2 _ _ _ _ Hcoupl
  intro P1 P2 HP12
  have := H (fun a' => ∃ a, f a = a' ∧ P1 a) (fun b' => ∃ a, R (f a) b' ∧ P1 a)
    (fun a' b' hR ⟨a, ha, hP⟩ => ⟨a, by rw [ha]; exact hR, hP⟩)
  rw [prob_dmap, prob_dmap] at this
  have hm1 : prob μ1 (fun a => decide (P1 a)) ≤
      prob μ1 (fun a => decide (∃ a', f a' = f a ∧ P1 a')) :=
    prob_mono_event μ1 fun a ha => by
      simp only [decide_eq_true_eq] at ha ⊢
      exact ⟨a, rfl, ha⟩
  have hm2 : prob μ2 (fun b => decide (∃ a, R (f a) (g b) ∧ P1 a)) ≤
      prob μ2 (fun b => decide (P2 b)) :=
    prob_mono_event μ2 fun b hb => by
      simp only [decide_eq_true_eq] at hb ⊢
      obtain ⟨a, hR, hP⟩ := hb
      exact HP12 a b hR hP
  calc _ ≤ _ := hm1
    _ ≤ _ := this
    _ ≤ _ := by gcongr

/-- Rocq: `ARcoupl_eq_trans_l`. -/
theorem ARcoupl_eq_trans_l (μ1 μ2 : Distr α) (μ3 : Distr β) (R : α → β → Prop)
    (ε1 ε2 : ℝ≥0∞) (Heq : ARcoupl μ1 μ2 (· = ·) ε1) (HR : ARcoupl μ2 μ3 R ε2) :
    ARcoupl μ1 μ3 R (ε1 + ε2) := by
  intro f g Hf Hg Hfg
  calc _ ≤ ∑' a, μ2 a * f a + ε1 := Heq f f Hf Hf fun _ _ h => h ▸ le_rfl
    _ ≤ ∑' b, μ3 b * g b + ε2 + ε1 := by gcongr; exact HR f g Hf Hg Hfg
    _ = _ := by ring

/-- Rocq: `ARcoupl_eq_trans_r`. -/
theorem ARcoupl_eq_trans_r (μ1 : Distr α) (μ2 μ3 : Distr β) (R : α → β → Prop)
    (ε1 ε2 : ℝ≥0∞) (HR : ARcoupl μ1 μ2 R ε1) (Heq : ARcoupl μ2 μ3 (· = ·) ε2) :
    ARcoupl μ1 μ3 R (ε1 + ε2) := by
  intro f g Hf Hg Hfg
  calc _ ≤ ∑' b, μ2 b * g b + ε1 := HR f g Hf Hg Hfg
    _ ≤ ∑' b, μ3 b * g b + ε2 + ε1 := by gcongr; exact Heq g g Hg Hg fun _ _ h => h ▸ le_rfl
    _ = _ := by ring

/-- Rocq: `ARcoupl_from_eq_Rcoupl` (the hypothesis `0 <= ε` is dropped). -/
theorem ARcoupl_from_eq_Rcoupl (μ1 μ2 : Distr α) (ε : ℝ≥0∞) (Hcpl : Rcoupl μ1 μ2 (· = ·)) :
    ARcoupl μ1 μ2 (· = ·) ε := by
  rw [Rcoupl_eq_elim μ1 μ2 Hcpl]
  exact ARcoupl_mon_grading _ _ _ 0 ε zero_le (ARcoupl_eq μ2)

/-- Rocq: `ARcoupl_eq_0`. -/
theorem ARcoupl_eq_0 (μ1 μ2 : Distr α) (h : ∀ x, μ1 x ≤ μ2 x) : ARcoupl μ1 μ2 (· = ·) 0 := by
  intro f g _ _ Hfg
  rw [add_zero]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' (h a) (Hfg a a rfl)

/-! ## Uniform distributions -/

/-- Rocq: `ARcoupl_dunif` (the `Bij` instance becomes a hypothesis). -/
theorem ARcoupl_dunif (N : ℕ) (f : Fin N → Fin N) (hf : Function.Bijective f) :
    ARcoupl (dunif N) (dunif N) (fun n m => m = f n) 0 := by
  intro g h _ _ Hgh
  rw [add_zero, ← (Equiv.ofBijective f hf).tsum_eq (fun b => dunif N b * h b)]
  exact ENNReal.tsum_le_tsum fun a => by
    simp only [dunif_pmf, Equiv.ofBijective_apply]
    gcongr
    exact Hgh a (f a) rfl

/-- Rocq: `ARcoupl_Bij`. -/
theorem ARcoupl_Bij (N : ℕ) (f : Fin N → Fin N) (_hf : Function.Bijective f) (ε : ℝ≥0∞) :
    ARcoupl (dunif N) (dunif N) (fun n m => m = f n) ε ↔
      ARcoupl (dmap f (dunif N)) (dmap id (dunif N)) (· = ·) ε := by
  have hid : dmap id (dunif N) = dunif N := dmap_id _
  constructor
  · intro H1
    refine ARcoupl_map f id _ _ (· = ·) ε ?_
    exact ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)
      (fun x y h => by rw [h]; rfl) le_rfl H1
  · intro H1
    rw [hid] at H1
    have H0 : ARcoupl (dmap id (dunif N)) (dmap f (dunif N)) (fun n m => m = f n) 0 :=
      ARcoupl_map id f _ _ _ 0 (ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)
        (fun x y h => by rw [h]; rfl) le_rfl (ARcoupl_eq (dunif N)))
    rw [hid] at H0
    simpa using ARcoupl_eq_trans_r _ _ _ _ 0 ε H0 H1

/-- Rocq: `ARcoupl_dunif_leq_inj`. -/
theorem ARcoupl_dunif_leq_inj (N M : ℕ) (h : Fin N → Fin M) (hinj : Function.Injective h)
    (Hleq : 0 < N ∧ N ≤ M) :
    ARcoupl (dunif N) (dunif M) (fun n m => m = h n) (((M : ℝ≥0∞) - N) / M) := by
  intro f g _ Hg Hfg
  simp only [dunif_pmf]
  rw [tsum_fintype, tsum_fintype]
  have h1 : ∑ n, (N : ℝ≥0∞)⁻¹ * f n ≤ ∑ n, (N : ℝ≥0∞)⁻¹ * g (h n) :=
    Finset.sum_le_sum fun n _ => by gcongr; exact Hfg n (h n) rfl
  have h2 : ∑ n, (M : ℝ≥0∞)⁻¹ * g (h n) ≤ ∑ m, (M : ℝ≥0∞)⁻¹ * g m := by
    classical
    rw [← Finset.sum_image (f := fun m => (M : ℝ≥0∞)⁻¹ * g m) (fun x _ y _ hxy => hinj hxy)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  set S := ∑ n, g (h n) with hSdef
  have hS : S ≤ N := (Finset.sum_le_sum fun n _ => Hg (h n)).trans (by simp)
  have key : (N : ℝ≥0∞)⁻¹ * S ≤ (M : ℝ≥0∞)⁻¹ * S + ((M : ℝ≥0∞) - N) / M := by
    have hSt : S ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) hS
    have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast Hleq.1.ne'
    have hM0 : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Hleq.1.trans_le Hleq.2).ne'
    have hNM : (N : ℝ≥0∞) ≤ M := by exact_mod_cast Hleq.2
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_div, ENNReal.toReal_sub_of_le hNM (ENNReal.natCast_ne_top _),
      ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    have hs0 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
    have hsN : S.toReal ≤ N := by
      have := ENNReal.toReal_mono (ENNReal.natCast_ne_top N) hS
      simpa using this
    have hN : (0 : ℝ) < N := by exact_mod_cast Hleq.1
    have hNM' : (N : ℝ) ≤ M := by exact_mod_cast Hleq.2
    have hM : (0 : ℝ) < M := hN.trans_le hNM'
    rw [inv_mul_le_iff₀ hN]
    field_simp
    nlinarith
  calc ∑ n, (N : ℝ≥0∞)⁻¹ * f n ≤ ∑ n, (N : ℝ≥0∞)⁻¹ * g (h n) := h1
    _ = (N : ℝ≥0∞)⁻¹ * S := by rw [Finset.mul_sum]
    _ ≤ (M : ℝ≥0∞)⁻¹ * S + ((M : ℝ≥0∞) - N) / M := key
    _ = ∑ n, (M : ℝ≥0∞)⁻¹ * g (h n) + ((M : ℝ≥0∞) - N) / M := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

/-- Rocq: `ARcoupl_dunif_leq`. -/
theorem ARcoupl_dunif_leq (N M : ℕ) (Hleq : 0 < N ∧ N ≤ M) :
    ARcoupl (dunif N) (dunif M) (fun n m => (n : ℕ) = m) (((M : ℝ≥0∞) - N) / M) :=
  ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) (fun n m h => by subst h; rfl) le_rfl
    (ARcoupl_dunif_leq_inj N M (Fin.castLE Hleq.2) (Fin.castLE_injective _) Hleq)

/-- Rocq: `ARcoupl_dunif_leq_rev_inj`. Note the asymmetry on the error w.r.t. the previous
lemma. -/
theorem ARcoupl_dunif_leq_rev_inj (N M : ℕ) (h : Fin M → Fin N) (hinj : Function.Injective h)
    (Hleq : 0 < M ∧ M ≤ N) :
    ARcoupl (dunif N) (dunif M) (fun n m => n = h m) (((N : ℝ≥0∞) - M) / N) := by
  classical
  intro f g Hf _ Hfg
  simp only [dunif_pmf]
  rw [tsum_fintype, tsum_fintype, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsplit : ∑ n, f n ≤ ∑ m, g m + ((N : ℝ≥0∞) - M) := by
    rw [← Finset.sum_add_sum_compl (Finset.univ.image h)]
    gcongr
    · rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
      exact Finset.sum_le_sum fun m _ => Hfg (h m) m rfl
    · calc ∑ x ∈ (Finset.univ.image h)ᶜ, f x ≤ ∑ x ∈ (Finset.univ.image h)ᶜ, (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun x _ => Hf x
        _ = (((Finset.univ.image h)ᶜ.card : ℕ) : ℝ≥0∞) := by simp
        _ = (N : ℝ≥0∞) - M := by
            rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ,
              Fintype.card_fin, Fintype.card_fin, ENNReal.natCast_sub]
  calc (N : ℝ≥0∞)⁻¹ * ∑ n, f n ≤ (N : ℝ≥0∞)⁻¹ * (∑ m, g m + ((N : ℝ≥0∞) - M)) := by gcongr
    _ = (N : ℝ≥0∞)⁻¹ * ∑ m, g m + ((N : ℝ≥0∞) - M) / N := by
        rw [mul_add, ENNReal.div_eq_inv_mul]
    _ ≤ (M : ℝ≥0∞)⁻¹ * ∑ m, g m + ((N : ℝ≥0∞) - M) / N := by
        gcongr
        exact_mod_cast Hleq.2

/-- Rocq: `ARcoupl_dunif_leq_rev`. -/
theorem ARcoupl_dunif_leq_rev (N M : ℕ) (Hleq : 0 < M ∧ M ≤ N) :
    ARcoupl (dunif N) (dunif M) (fun n m => (n : ℕ) = m) (((N : ℝ≥0∞) - M) / N) :=
  ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) (fun n m h => by subst h; rfl) le_rfl
    (ARcoupl_dunif_leq_rev_inj N M (Fin.castLE Hleq.2) (Fin.castLE_injective _) Hleq)

/-- `N * N⁻¹ = 1` for positive `N` (helper). -/
theorem natCast_mul_inv_cancel (N : ℕ) (hN : 0 < N) : (N : ℝ≥0∞) * (N : ℝ≥0∞)⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

/-- Summing `N⁻¹ * (c + [n = x])` over `Fin N` (helper). -/
theorem sum_dunif_add_indicator (N : ℕ) (x : Fin N) (c : Fin N → ℝ≥0∞) :
    ∑' n : Fin N, (N : ℝ≥0∞)⁻¹ * (c n + if n = x then 1 else 0) =
      ∑' n : Fin N, (N : ℝ≥0∞)⁻¹ * c n + 1 / N := by
  rw [tsum_fintype, tsum_fintype]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, one_div]

/-- Rocq: `ARcoupl_dunif_no_coll_l`. -/
theorem ARcoupl_dunif_no_coll_l (v : α) (N : ℕ) (x : Fin N) (hN : 0 < N) :
    ARcoupl (dunif N) (dret v) (fun m n => m ≠ x ∧ n = v) (1 / N) := by
  intro f g Hf _ Hfg
  rw [SeriesC_dret_mul]
  simp only [dunif_pmf]
  calc ∑' n, (N : ℝ≥0∞)⁻¹ * f n ≤ ∑' n : Fin N, (N : ℝ≥0∞)⁻¹ * (g v + if n = x then 1 else 0) :=
        ENNReal.tsum_le_tsum fun n => by
          gcongr
          by_cases hn : n = x
          · simp only [hn, ite_true]; exact (Hf x).trans le_add_self
          · simp only [hn, ite_false, add_zero]; exact Hfg n v ⟨hn, rfl⟩
    _ = ∑' n : Fin N, (N : ℝ≥0∞)⁻¹ * g v + 1 / N := sum_dunif_add_indicator N x _
    _ = g v + 1 / N := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← mul_assoc, natCast_mul_inv_cancel N hN, one_mul]

/-- Rocq: `ARcoupl_dunif_no_coll_l'`. -/
theorem ARcoupl_dunif_no_coll_l' (N : ℕ) (x : Fin N) (hN : 0 < N) :
    ARcoupl (dunif N) (dret x) (fun m n => m ≠ x ∧ n = x) (1 / N) :=
  ARcoupl_dunif_no_coll_l x N x hN

/-- Rocq: `ARcoupl_dunif_no_coll_r`. -/
theorem ARcoupl_dunif_no_coll_r (v : α) (N : ℕ) (x : Fin N) (hN : 0 < N) :
    ARcoupl (dret v) (dunif N) (fun m n => m = v ∧ n ≠ x) (1 / N) := by
  intro f g Hf _ Hfg
  rw [SeriesC_dret_mul]
  simp only [dunif_pmf]
  calc f v = ∑' _ : Fin N, (N : ℝ≥0∞)⁻¹ * f v := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← mul_assoc, natCast_mul_inv_cancel N hN, one_mul]
    _ ≤ ∑' n : Fin N, (N : ℝ≥0∞)⁻¹ * (g n + if n = x then 1 else 0) :=
        ENNReal.tsum_le_tsum fun n => by
          gcongr
          by_cases hn : n = x
          · simp only [hn, ite_true]; exact (Hf v).trans le_add_self
          · simp only [hn, ite_false, add_zero]; exact Hfg v n ⟨rfl, hn⟩
    _ = _ := sum_dunif_add_indicator N x _

/-- Rocq: `ARcoupl_dunif_no_coll_r'`. -/
theorem ARcoupl_dunif_no_coll_r' (N : ℕ) (x : Fin N) (hN : 0 < N) :
    ARcoupl (dret x) (dunif N) (fun m n => m = x ∧ n ≠ x) (1 / N) :=
  ARcoupl_dunif_no_coll_r x N x hN

/-! ## Relation with graded predicate liftings -/

/-- Rocq: `UB_to_ARcoupl`. -/
theorem UB_to_ARcoupl (μ1 : Distr α) (P : α → Prop) (ε : ℝ≥0∞) (Hub : pgl μ1 P ε) :
    ARcoupl μ1 (dret ()) (fun a _ => P a) ε := by
  classical
  rw [pgl_unfold] at Hub
  intro f g Hf _ Hfg
  rw [SeriesC_dret_mul]
  calc ∑' a, μ1 a * f a
      ≤ ∑' a, (μ1 a * g () + (if !decide (P a) then μ1 a else 0)) :=
        ENNReal.tsum_le_tsum fun a => by
          by_cases hP : P a
          · simp only [hP, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, add_zero]
            gcongr; exact Hfg a () hP
          · simp only [hP, decide_false, Bool.not_false, ite_true]
            exact (mul_le_of_le_one_right' (Hf a)).trans le_add_self
    _ = (∑' a, μ1 a) * g () + prob μ1 (fun a => !decide (P a)) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]; rfl
    _ ≤ g () + ε := by
        gcongr
        exact mul_le_of_le_one_left zero_le μ1.mass_le_one

/-- Rocq: `ARcoupl_to_UB`. -/
theorem ARcoupl_to_UB (μ1 : Distr α) (μ2 : Distr β) (P : α → Prop) (ε : ℝ≥0∞)
    (Har : ARcoupl μ1 μ2 (fun a _ => P a) ε) : pgl μ1 P ε := by
  classical
  rw [pgl_unfold]
  have := Har (fun a => if P a then 0 else 1) (fun _ => 0) (fun a => by split_ifs <;> simp)
    (fun _ => zero_le) (fun a b hP => by simp [hP])
  simp only [mul_zero, tsum_zero, zero_add] at this
  refine le_trans (le_of_eq ?_) this
  unfold prob
  refine tsum_congr fun a => ?_
  by_cases hP : P a <;> simp [hP]

/-- Rocq: `up_to_bad_lhs`. -/
theorem up_to_bad_lhs (μ1 : Distr α) (μ2 : Distr β) (P : α → Prop) (Q : α → β → Prop)
    (ε ε' : ℝ≥0∞) (Hcpl : ARcoupl μ1 μ2 (fun a b => P a → Q a b) ε) (Hub : pgl μ1 P ε') :
    ARcoupl μ1 μ2 Q (ε + ε') := by
  classical
  rw [pgl_unfold] at Hub
  intro f g Hf Hg Hfg
  have key := Hcpl (fun a => if P a then f a else 0) g
    (fun a => by split_ifs; exacts [Hf a, zero_le]) Hg
    (fun a b h => by split_ifs with hP; exacts [Hfg a b (h hP), zero_le])
  calc ∑' a, μ1 a * f a
      ≤ ∑' a, (μ1 a * (if P a then f a else 0) + (if !decide (P a) then μ1 a else 0)) :=
        ENNReal.tsum_le_tsum fun a => by
          by_cases hP : P a
          · simp [hP]
          · simp only [hP, ite_false, mul_zero, decide_false, Bool.not_false, ite_true, zero_add]
            exact mul_le_of_le_one_right' (Hf a)
    _ = ∑' a, μ1 a * (if P a then f a else 0) + prob μ1 (fun a => !decide (P a)) :=
        ENNReal.tsum_add
    _ ≤ ∑' b, μ2 b * g b + ε + ε' := add_le_add key Hub
    _ = _ := add_assoc _ _ _

/-- Rocq: `up_to_bad_rhs`. -/
theorem up_to_bad_rhs (μ1 : Distr α) (μ2 : Distr β) (P : β → Prop) (Q : α → β → Prop)
    (ε ε' : ℝ≥0∞) (Hcpl : ARcoupl μ1 μ2 (fun a b => P b → Q a b) ε) (Hub : pgl μ2 P ε') :
    ARcoupl μ1 μ2 Q (ε + ε') := by
  classical
  rw [pgl_unfold] at Hub
  intro f g Hf Hg Hfg
  have key := Hcpl f (fun b => if P b then g b else 1) Hf
    (fun b => by split_ifs; exacts [Hg b, le_rfl])
    (fun a b h => by split_ifs with hP; exacts [Hfg a b (h hP), Hf a])
  calc ∑' a, μ1 a * f a ≤ ∑' b, μ2 b * (if P b then g b else 1) + ε := key
    _ ≤ ∑' b, (μ2 b * g b + (if !decide (P b) then μ2 b else 0)) + ε := by
        gcongr ?_ + _
        refine ENNReal.tsum_le_tsum fun b => ?_
        by_cases hP : P b
        · simp [hP]
        · simp [hP]
    _ = ∑' b, μ2 b * g b + prob μ2 (fun b => !decide (P b)) + ε := by rw [ENNReal.tsum_add]; rfl
    _ ≤ ∑' b, μ2 b * g b + ε' + ε := by gcongr
    _ = _ := by ring

/-! ## Relation with exact couplings -/

/-- Rocq: `ARcoupl_refRcoupl`. -/
theorem ARcoupl_refRcoupl (μ1 : Distr α) (μ2 : Distr β) (ψ : α → β → Prop)
    (H : refRcoupl μ1 μ2 ψ) : ARcoupl μ1 μ2 ψ 0 := by
  obtain ⟨μ, ⟨hL, hR⟩, Hs⟩ := H
  subst hL
  intro f g _ _ Hfg
  rw [add_zero]
  calc ∑' a, lmarg μ a * f a = ∑' a, ∑' b, μ (a, b) * f a := by
        simp_rw [lmarg_pmf, ENNReal.tsum_mul_right]
    _ ≤ ∑' a, ∑' b, μ (a, b) * g b :=
        ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun b => by
          by_cases hp : 0 < μ (a, b)
          · gcongr; exact Hfg a b (Hs _ hp)
          · simp [pmf_eq_0_not_gt_0 μ _ hp]
    _ = ∑' b, rmarg μ b * g b := by
        rw [ENNReal.tsum_comm]; simp_rw [rmarg_pmf, ENNReal.tsum_mul_right]
    _ ≤ _ := ENNReal.tsum_le_tsum fun b => by gcongr; exact hR b

/-- Rocq: `ARcoupl_exact`. -/
theorem ARcoupl_exact (μ1 : Distr α) (μ2 : Distr β) (ψ : α → β → Prop)
    (H : Rcoupl μ1 μ2 ψ) : ARcoupl μ1 μ2 ψ 0 :=
  ARcoupl_refRcoupl _ _ _ (Rcoupl_refRcoupl _ _ _ H)

/-- Rocq: `ARcoupl_limit`. -/
theorem ARcoupl_limit (μ1 : Distr α) (μ2 : Distr β) (ε : ℝ≥0∞) (ψ : α → β → Prop)
    (Hlimit : ∀ ε', ε < ε' → ARcoupl μ1 μ2 ψ ε') : ARcoupl μ1 μ2 ψ ε := by
  intro f g Hf Hg Hfg
  rcases eq_or_ne ε ⊤ with rfl | hε
  · simp
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have := Hlimit (ε + δ) (ENNReal.lt_add_right hε (by exact_mod_cast hδ.ne')) f g Hf Hg Hfg
  rwa [← add_assoc] at this

/-- Rocq: `ARcoupl_antisym`. -/
theorem ARcoupl_antisym (μ1 μ2 : Distr α) (H1 : ARcoupl μ1 μ2 (· = ·) 0)
    (H2 : ARcoupl μ2 μ1 (· = ·) 0) : μ1 = μ2 :=
  distr_ext fun a => le_antisymm (by simpa using ARcoupl_eq_elim _ _ _ H1 a)
    (by simpa using ARcoupl_eq_elim _ _ _ H2 a)

/-- Rocq: `ARcoupl_tight`. (In `ℝ≥0∞` the `if` is redundant, but it is kept for fidelity.) -/
theorem ARcoupl_tight (μ1 μ2 : Distr α) (ε : ℝ≥0∞) :
    ARcoupl μ1 μ2 (· = ·) ε ↔
      ∑' x, (if μ2 x ≤ μ1 x then μ1 x - μ2 x else 0) ≤ ε := by
  constructor
  · intro H
    let F : α → ℝ≥0∞ := fun x => if μ2 x ≤ μ1 x then 1 else 0
    have hF : ∀ x, F x ≤ 1 := fun x => by simp only [F]; split_ifs <;> simp
    have := H F F hF hF fun _ _ h => h ▸ le_rfl
    have e : ∑' x, μ1 x * F x =
        ∑' x, (if μ2 x ≤ μ1 x then μ1 x - μ2 x else 0) + ∑' x, μ2 x * F x := by
      rw [← ENNReal.tsum_add]
      refine tsum_congr fun x => ?_
      simp only [F]
      split_ifs with h
      · simp [tsub_add_cancel_of_le h]
      · simp
    rw [e] at this
    have hA : ∑' x, μ2 x * F x ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (SeriesC_mul_le_one μ2 F hF)
    exact ENNReal.le_of_add_le_add_right hA (this.trans_eq (add_comm _ _))
  · intro HD f g Hf _ Hfg
    calc ∑' x, μ1 x * f x
        ≤ ∑' x, (μ2 x * g x + if μ2 x ≤ μ1 x then μ1 x - μ2 x else 0) :=
          ENNReal.tsum_le_tsum fun x => by
            have hfg := Hfg x x rfl
            split_ifs with h
            · calc μ1 x * f x = (μ1 x - μ2 x) * f x + μ2 x * f x := by
                    rw [← add_mul, tsub_add_cancel_of_le h]
                _ ≤ (μ1 x - μ2 x) * 1 + μ2 x * g x := by gcongr; exact Hf x
                _ = _ := by rw [mul_one, add_comm]
            · rw [add_zero]
              exact mul_le_mul' (not_le.1 h).le hfg
      _ = ∑' x, μ2 x * g x + ∑' x, (if μ2 x ≤ μ1 x then μ1 x - μ2 x else 0) := ENNReal.tsum_add
      _ ≤ _ := by gcongr

/-- Rocq: `ARcoupl_swap`. -/
theorem ARcoupl_swap (μ1 μ2 : Distr α) (ε : ℝ≥0∞) (Heq : ∑' a, μ2 a ≤ ∑' a, μ1 a)
    (H : ARcoupl μ1 μ2 (· = ·) ε) : ARcoupl μ2 μ1 (· = ·) ε := by
  rw [ARcoupl_tight] at H ⊢
  refine le_trans ?_ H
  have hpt : ∀ x, (if μ1 x ≤ μ2 x then μ2 x - μ1 x else 0) + μ1 x =
      (if μ2 x ≤ μ1 x then μ1 x - μ2 x else 0) + μ2 x := by
    intro x
    split_ifs with h1 h2 h2
    · rw [tsub_add_cancel_of_le h1, tsub_add_cancel_of_le h2]; exact le_antisymm h2 h1
    · rw [tsub_add_cancel_of_le h1, zero_add]
    · rw [tsub_add_cancel_of_le h2, zero_add]
    · exact absurd (le_total (μ1 x) (μ2 x)) (by simp [h1, h2])
  have hsum : ∑' x, (if μ1 x ≤ μ2 x then μ2 x - μ1 x else 0) + ∑' x, μ1 x =
      ∑' x, (if μ2 x ≤ μ1 x then μ1 x - μ2 x else 0) + ∑' x, μ2 x := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    exact tsum_congr hpt
  refine ENNReal.le_of_add_le_add_right (SeriesC_ne_top μ1) ?_
  rw [hsum]
  gcongr

/-- Rocq: `ARcoupl_symmetric`. -/
theorem ARcoupl_symmetric (μ1 μ2 : Distr α) (ε : ℝ≥0∞) (H : ∑' a, μ1 a = ∑' a, μ2 a) :
    ARcoupl μ1 μ2 (· = ·) ε ↔ ARcoupl μ2 μ1 (· = ·) ε :=
  ⟨ARcoupl_swap _ _ _ H.ge, ARcoupl_swap _ _ _ H.le⟩

/-- Rocq: `ARcoupl_dunif_avoid`. -/
theorem ARcoupl_dunif_avoid (N : ℕ) (l : List (Fin N)) (Hl : l.Nodup) :
    ARcoupl (dunif N) (dunif N) (fun x y => x ∉ l ∧ x = y) (l.length / N) := by
  classical
  intro f g Hf _ Hfg
  simp only [dunif_pmf]
  rw [tsum_fintype, tsum_fintype]
  calc ∑ x, (N : ℝ≥0∞)⁻¹ * f x
      ≤ ∑ x, ((N : ℝ≥0∞)⁻¹ * g x + (N : ℝ≥0∞)⁻¹ * if x ∈ l then 1 else 0) :=
        Finset.sum_le_sum fun x _ => by
          rw [← mul_add]
          gcongr
          by_cases hx : x ∈ l
          · simp only [hx, ite_true]; exact (Hf x).trans le_add_self
          · simp only [hx, ite_false, add_zero]; exact Hfg x x ⟨hx, rfl⟩
    _ = ∑ x, (N : ℝ≥0∞)⁻¹ * g x + l.length / N := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole,
          ENNReal.div_eq_inv_mul]
        congr 3
        rw [← List.toFinset_card_of_nodup Hl]
        congr 1
        ext x
        simp

end Prob
