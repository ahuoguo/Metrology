module

public import Metrology.Prob.Distribution
public import Metrology.Prob.Prelude.StdppExt

/-!
# Exact couplings of discrete distributions

Ported from clutch/theories/prob/couplings.v

A coupling of `μ₁ : Distr α` and `μ₂ : Distr β` is a distribution on `α × β` whose marginals are
`μ₁` and `μ₂`. An `R`-coupling additionally has support inside `R`. A refinement coupling
(`refRcoupl`) only requires the right marginal to be pointwise below `μ₂`.

Compared with the Rocq development, all summability and non-negativity side conditions disappear
(masses are `ℝ≥0∞`), and `μ p > 0` is written `0 < μ p`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Prob

variable {α β γ δ ε α' β' : Type*} [Countable α] [Countable β] [Countable γ] [Countable δ]
  [Countable ε] [Countable α'] [Countable β']

/-! ## Definitions -/

section coupl

/-- Rocq: `is_coupl`. -/
def is_coupl (μ1 : Distr α) (μ2 : Distr β) (μ : Distr (α × β)) : Prop :=
  lmarg μ = μ1 ∧ rmarg μ = μ2

/-- Rocq: `ex_coupl`. -/
def ex_coupl (μ1 : Distr α) (μ2 : Distr β) : Prop :=
  ∃ μ : Distr (α × β), is_coupl μ1 μ2 μ

end coupl

section Rcoupl

/-- Rocq: `is_Rcoupl`. -/
def is_Rcoupl (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) (μ : Distr (α × β)) : Prop :=
  is_coupl μ1 μ2 μ ∧ ∀ p : α × β, 0 < μ p → R p.1 p.2

/-- Rocq: `Rcoupl`. -/
def Rcoupl (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) : Prop :=
  ∃ μ : Distr (α × β), is_Rcoupl μ1 μ2 R μ

end Rcoupl

/-! ## Auxiliary facts about marginals of binds (not in Rocq, used to replace Fubini arguments) -/

section aux

/-- The left marginal of a bind is the bind of the left marginals. -/
theorem lmarg_dbind (Ch : γ → Distr (α × β)) (μ : Distr γ) :
    lmarg (μ ≫= Ch) = μ ≫= fun p => lmarg (Ch p) := dmap_dbind _ _ _

/-- The right marginal of a bind is the bind of the right marginals. -/
theorem rmarg_dbind (Ch : γ → Distr (α × β)) (μ : Distr γ) :
    rmarg (μ ≫= Ch) = μ ≫= fun p => rmarg (Ch p) := dmap_dbind _ _ _

/-- Binding a function of the first component factors through the left marginal. -/
theorem dbind_fst (μ : Distr (α × β)) (f : α → Distr γ) :
    (μ ≫= fun p => f p.1) = lmarg μ ≫= f := by
  rw [lmarg, dmap, ← dbind_assoc]; simp only [dret_id_left]

/-- Binding a function of the second component factors through the right marginal. -/
theorem dbind_snd (μ : Distr (α × β)) (f : β → Distr γ) :
    (μ ≫= fun p => f p.2) = rmarg μ ≫= f := by
  rw [rmarg, dmap, ← dbind_assoc]; simp only [dret_id_left]

/-- A positive left-marginal value comes from a positive point of the joint distribution. -/
theorem lmarg_pos_of_pos (μ : Distr (α × β)) (a : α) (b : β) (h : 0 < μ (a, b)) :
    0 < lmarg μ a :=
  (dmap_pos _ _ _).2 ⟨(a, b), rfl, h⟩

/-- A positive right-marginal value comes from a positive point of the joint distribution. -/
theorem rmarg_pos_of_pos (μ : Distr (α × β)) (a : α) (b : β) (h : 0 < μ (a, b)) :
    0 < rmarg μ b :=
  (dmap_pos _ _ _).2 ⟨(a, b), rfl, h⟩

end aux

/-! ## Couplings -/

section is_coupl

/-- Rocq: `is_Rcoupl_is_coupl`. -/
theorem is_Rcoupl_is_coupl (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) (μ : Distr (α × β))
    (h : is_Rcoupl μ1 μ2 R μ) : is_coupl μ1 μ2 μ := h.1

/-- Rocq: `is_coupl_mass_l`. -/
theorem is_coupl_mass_l (μ1 : Distr α) (μ2 : Distr β) (μ : Distr (α × β))
    (h : is_coupl μ1 μ2 μ) : ∑' p, μ p = ∑' a, μ1 a := by
  rw [← h.1, lmarg, dmap_mass]

/-- Rocq: `is_coupl_mass_r`. -/
theorem is_coupl_mass_r (μ1 : Distr α) (μ2 : Distr β) (μ : Distr (α × β))
    (h : is_coupl μ1 μ2 μ) : ∑' p, μ p = ∑' b, μ2 b := by
  rw [← h.2, rmarg, dmap_mass]

/-- Rocq: `is_coupl_mass_eq`. -/
theorem is_coupl_mass_eq (μ1 : Distr α) (μ2 : Distr β) (μ : Distr (α × β))
    (h : is_coupl μ1 μ2 μ) : ∑' a, μ1 a = ∑' b, μ2 b := by
  rw [← is_coupl_mass_l μ1 μ2 μ h, is_coupl_mass_r μ1 μ2 μ h]

/-- Rocq: `is_coupl_dret`. -/
theorem is_coupl_dret (a : α) (b : β) : is_coupl (dret a) (dret b) (dret (a, b)) :=
  ⟨by rw [lmarg, dmap_dret], by rw [rmarg, dmap_dret]⟩

end is_coupl

section ex_coupl

/-- Rocq: `coupl_dret`. -/
theorem coupl_dret (a : α) (b : β) : ex_coupl (dret a) (dret b) :=
  ⟨_, is_coupl_dret a b⟩

/-- Rocq: `ex_coupl_sym`. -/
theorem ex_coupl_sym (μ1 : Distr α) (μ2 : Distr β) (h : ex_coupl μ1 μ2) : ex_coupl μ2 μ1 := by
  obtain ⟨μ, hL, hR⟩ := h
  exact ⟨dswap μ, by rw [lmarg_dswap]; exact hR, by rw [rmarg_dswap]; exact hL⟩

/-- Rocq: `ex_coupl_dbind`. -/
theorem ex_coupl_dbind (f : α → Distr α') (g : β → Distr β') (μ1 : Distr α) (μ2 : Distr β)
    (Hfg : ∀ a b, ex_coupl (f a) (g b)) (Hμ : ex_coupl μ1 μ2) :
    ex_coupl (μ1 ≫= f) (μ2 ≫= g) := by
  obtain ⟨μ, hL, hR⟩ := Hμ
  choose Ch HCh using fun p : α × β => Hfg p.1 p.2
  refine ⟨μ ≫= Ch, ?_, ?_⟩
  · rw [lmarg_dbind, dbind_ext_right μ _ (fun p => f p.1) (fun p => (HCh p).1), dbind_fst, hL]
  · rw [rmarg_dbind, dbind_ext_right μ _ (fun p => g p.2) (fun p => (HCh p).2), dbind_snd, hR]

end ex_coupl

section is_Rcoupl

/-- Rocq: `is_Rcoupl_dret`. -/
theorem is_Rcoupl_dret (a : α) (b : β) (R : α → β → Prop) (h : R a b) :
    is_Rcoupl (dret a) (dret b) R (dret (a, b)) := by
  refine ⟨is_coupl_dret a b, fun p hp => ?_⟩
  rw [dret_pos _ _ hp]; exact h

end is_Rcoupl

section Rcoupl

/-- Rocq: `Rcoupl_dret`. -/
theorem Rcoupl_dret (a : α) (b : β) (R : α → β → Prop) (h : R a b) :
    Rcoupl (dret a) (dret b) R :=
  ⟨_, is_Rcoupl_dret a b R h⟩

/-- Rocq: `Rcoupl_mass_eq`. -/
theorem Rcoupl_mass_eq (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) (h : Rcoupl μ1 μ2 R) :
    ∑' a, μ1 a = ∑' b, μ2 b := by
  obtain ⟨μ, hμ, -⟩ := h
  exact is_coupl_mass_eq μ1 μ2 μ hμ

/-- Rocq: `Rcoupl_eq`. -/
theorem Rcoupl_eq (μ1 : Distr α) : Rcoupl μ1 μ1 (· = ·) := by
  classical
  refine ⟨ddiag μ1, ⟨ddiag_lmarg μ1, ddiag_rmarg μ1⟩, fun p hp => ?_⟩
  rw [ddiag_pmf] at hp
  by_contra hne
  simp [hne] at hp

/-- Rocq: `Rcoupl_dbind`. -/
theorem Rcoupl_dbind (f : α → Distr α') (g : β → Distr β') (μ1 : Distr α) (μ2 : Distr β)
    (R : α → β → Prop) (S : α' → β' → Prop)
    (Hfg : ∀ a b, R a b → Rcoupl (f a) (g b) S) (Hμ : Rcoupl μ1 μ2 R) :
    Rcoupl (μ1 ≫= f) (μ2 ≫= g) S := by
  obtain ⟨μ, ⟨hL, hR⟩, HμS⟩ := Hμ
  have Hfg' : ∀ p : α × β, ∃ μ' : Distr (α' × β'),
      R p.1 p.2 → is_Rcoupl (f p.1) (g p.2) S μ' := by
    intro p
    by_cases hR : R p.1 p.2
    · obtain ⟨μ', hμ'⟩ := Hfg _ _ hR
      exact ⟨μ', fun _ => hμ'⟩
    · exact ⟨dzero, fun h => absurd h hR⟩
  choose Ch HCh using Hfg'
  refine ⟨μ ≫= Ch, ⟨?_, ?_⟩, ?_⟩
  · rw [lmarg_dbind, dbind_eq _ (fun p => f p.1) μ μ
      (fun p hp => (HCh p (HμS p hp)).1.1) (fun _ => rfl), dbind_fst, hL]
  · rw [rmarg_dbind, dbind_eq _ (fun p => g p.2) μ μ
      (fun p hp => (HCh p (HμS p hp)).1.2) (fun _ => rfl), dbind_snd, hR]
  · intro q hq
    obtain ⟨p, hq', hp⟩ := (dbind_pos _ _ _).1 hq
    exact (HCh p (HμS p hp)).2 q hq'

/-- Rocq: `Rcoupl_eq_elim`. -/
theorem Rcoupl_eq_elim (μ1 μ2 : Distr α) (h : Rcoupl μ1 μ2 (· = ·)) : μ1 = μ2 := by
  obtain ⟨μ, ⟨hL, hR⟩, HμS⟩ := h
  rw [← hL, ← hR]
  ext a
  rw [lmarg_pmf, rmarg_pmf]
  refine tsum_congr fun b => ?_
  by_cases hab : a = b
  · subst hab; rfl
  · rw [pmf_eq_0_not_gt_0 μ (a, b) fun hp => hab (HμS _ hp),
      pmf_eq_0_not_gt_0 μ (b, a) fun hp => hab (HμS _ hp).symm]

/-- Rocq: `Rcoupl_eq_sym`. -/
theorem Rcoupl_eq_sym (μ1 μ2 : Distr α) (h : Rcoupl μ1 μ2 (· = ·)) : Rcoupl μ2 μ1 (· = ·) := by
  rw [Rcoupl_eq_elim μ1 μ2 h]; exact Rcoupl_eq μ2

/-- Rocq: `Rcoupl_eq_trans`. -/
theorem Rcoupl_eq_trans (μ1 μ2 μ3 : Distr α) (h12 : Rcoupl μ1 μ2 (· = ·))
    (h23 : Rcoupl μ2 μ3 (· = ·)) : Rcoupl μ1 μ3 (· = ·) := by
  rw [Rcoupl_eq_elim μ1 μ2 h12]; exact h23

/-- Rocq: `Rcoupl_mono`. -/
theorem Rcoupl_mono (μ1 : Distr α) (μ2 : Distr β) (R S : α → β → Prop) (h : Rcoupl μ1 μ2 R)
    (Hwk : ∀ a b, R a b → S a b) : Rcoupl μ1 μ2 S := by
  obtain ⟨μ, hμ, HμS⟩ := h
  exact ⟨μ, hμ, fun p hp => Hwk _ _ (HμS p hp)⟩

/-- Rocq: `Rcoupl_swap`. -/
theorem Rcoupl_swap (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) (h : Rcoupl μ1 μ2 R) :
    Rcoupl μ2 μ1 (flip R) := by
  obtain ⟨μ, ⟨hL, hR⟩, HμS⟩ := h
  refine ⟨dswap μ, ⟨by rw [lmarg_dswap, hR], by rw [rmarg_dswap, hL]⟩, ?_⟩
  rintro ⟨b, a⟩ hp
  exact HμS (a, b) (dswap_pos μ a b hp)

/-- Rocq: `Rcoupl_inhabited_l`. -/
theorem Rcoupl_inhabited_l (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop)
    (h : Rcoupl μ1 μ2 R) (hz : 0 < ∑' a, μ1 a) : ∃ a b, R a b := by
  obtain ⟨μ, hcpl, HR⟩ := h
  rw [← is_coupl_mass_l μ1 μ2 μ hcpl] at hz
  obtain ⟨⟨a, b⟩, hμ⟩ := SeriesC_gtz_ex _ hz
  exact ⟨a, b, HR _ hμ⟩

/-- Rocq: `Rcoupl_inhabited_r`. -/
theorem Rcoupl_inhabited_r (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop)
    (h : Rcoupl μ1 μ2 R) (hz : 0 < ∑' b, μ2 b) : ∃ a b, R a b := by
  obtain ⟨μ, hcpl, HR⟩ := h
  rw [← is_coupl_mass_r μ1 μ2 μ hcpl] at hz
  obtain ⟨⟨a, b⟩, hμ⟩ := SeriesC_gtz_ex _ hz
  exact ⟨a, b, HR _ hμ⟩

/-- Rocq: `Rcoupl_trivial`. -/
theorem Rcoupl_trivial (μ1 : Distr α) (μ2 : Distr β) (h1 : ∑' a, μ1 a = 1)
    (h2 : ∑' b, μ2 b = 1) : Rcoupl μ1 μ2 (fun _ _ => True) :=
  ⟨dprod μ1 μ2, ⟨lmarg_dprod μ1 μ2 h2, rmarg_dprod μ1 μ2 h1⟩, fun _ _ => trivial⟩

/-- Rocq: `Rcoupl_pos_R`. -/
theorem Rcoupl_pos_R (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) (h : Rcoupl μ1 μ2 R) :
    Rcoupl μ1 μ2 (fun a b => R a b ∧ 0 < μ1 a ∧ 0 < μ2 b) := by
  obtain ⟨μ, ⟨hL, hR⟩, HR⟩ := h
  refine ⟨μ, ⟨hL, hR⟩, ?_⟩
  rintro ⟨a, b⟩ hp
  refine ⟨HR _ hp, ?_, ?_⟩
  · rw [← hL]; exact lmarg_pos_of_pos μ a b hp
  · rw [← hR]; exact rmarg_pos_of_pos μ a b hp

/-- Rocq: `Rcoupl_dzero_dzero`. -/
theorem Rcoupl_dzero_dzero (R : α → β → Prop) : Rcoupl (dzero : Distr α) (dzero : Distr β) R :=
  ⟨dzero, ⟨lmarg_dzero, rmarg_dzero⟩, fun p hp => absurd hp (dzero_supp_empty p)⟩

/-- Rocq: `Rcoupl_dzero_r_inv`. -/
theorem Rcoupl_dzero_r_inv (μ1 : Distr α) (R : α → β → Prop) (h : Rcoupl μ1 dzero R) :
    μ1 = dzero := by
  apply SeriesC_zero_dzero
  rw [Rcoupl_mass_eq _ _ _ h, dzero_mass]

/-- Rocq: `Rcoupl_dzero_l_inv`. -/
theorem Rcoupl_dzero_l_inv (μ2 : Distr β) (R : α → β → Prop) (h : Rcoupl dzero μ2 R) :
    μ2 = dzero := by
  apply SeriesC_zero_dzero
  rw [← Rcoupl_mass_eq _ _ _ h, dzero_mass]

end Rcoupl

/-- Rocq: `Rcoupl_dmap`. -/
theorem Rcoupl_dmap (f : α → α') (g : β → β') (μ1 : Distr α) (μ2 : Distr β)
    (R : α' → β' → Prop) (h : Rcoupl μ1 μ2 (fun a a' => R (f a) (g a'))) :
    Rcoupl (dmap f μ1) (dmap g μ2) R :=
  Rcoupl_dbind _ _ _ _ _ _ (fun _ _ hab => Rcoupl_dret _ _ _ hab) h

/-- Rocq: `Rcoupl_dunif`. The Rocq `Bij f` instance becomes `Function.Bijective f`. -/
theorem Rcoupl_dunif (N : ℕ) (f : Fin N → Fin N) (hf : Function.Bijective f) :
    Rcoupl (dunif N) (dunif N) (fun n m => m = f n) := by
  refine ⟨dmap (fun x => (x, f x)) (dunif N), ⟨?_, ?_⟩, ?_⟩
  · rw [lmarg, dmap_comp]; exact dmap_id _
  · rw [rmarg, dmap_comp]
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    exact dmap_unif_nonzero N x _ _ hf.1 rfl
  · intro p hp
    obtain ⟨x, rfl, -⟩ := (dmap_pos _ _ _).1 hp
    rfl

/-- Rocq: `Rcoupl_fair_coin_dunifP`. -/
theorem Rcoupl_fair_coin_dunifP (μ : Distr α) (R : Bool → α → Prop)
    (Hcpl : Rcoupl fair_coin μ R) :
    Rcoupl (dunifP 1) μ (fun n a => R (fin_to_bool n) a) := by
  have h : dunifP 1 = dmap bool_to_fin fair_coin := by
    ext n
    have hb : ∀ b : Bool, dmap bool_to_fin fair_coin (bool_to_fin b) = 2⁻¹ := fun b =>
      dmap_elem_eq _ b _ _ bool_to_fin_inj rfl
    rw [dunifP_pmf]
    fin_cases n
    · exact (by norm_num : ((1 + 1 : ℕ) : ℝ≥0∞)⁻¹ = 2⁻¹).trans (hb false).symm
    · exact (by norm_num : ((1 + 1 : ℕ) : ℝ≥0∞)⁻¹ = 2⁻¹).trans (hb true).symm
  rw [h, ← dmap_id μ]
  apply Rcoupl_dmap
  simpa using Hcpl

/-- Rocq: `fair_conv_comb_dbind`. -/
theorem fair_conv_comb_dbind (f : α → Distr β) (μ1 μ2 : Distr α) :
    (fair_conv_comb μ1 μ2 ≫= f) = fair_conv_comb (μ1 ≫= f) (μ2 ≫= f) := by
  rw [fair_conv_comb, fair_conv_comb, ← dbind_assoc]
  congr 1
  funext b
  cases b <;> rfl

section Rcoupl_strength

variable (μ1 : Distr α) (μ2 : Distr β)

/-- Rocq: `Rcoupl_strength_l`. The Rocq pattern `λ '(d', a) b, ...` uses projections. -/
theorem Rcoupl_strength_l (R : α → β → Prop) (d : δ) (Hcpl : Rcoupl μ1 μ2 R) :
    Rcoupl (strength_l d μ1) μ2 (fun p b => p.1 = d ∧ R p.2 b) := by
  rw [strength_l, ← dmap_id μ2]
  apply Rcoupl_dmap
  exact Rcoupl_mono _ _ _ _ Hcpl fun _ _ h => ⟨rfl, h⟩

/-- Rocq: `Rcoupl_strength`. -/
theorem Rcoupl_strength (R : α → β → Prop) (d : δ) (e : ε) (Hcpl : Rcoupl μ1 μ2 R) :
    Rcoupl (strength_l d μ1) (strength_l e μ2) (fun p q => p.1 = d ∧ q.1 = e ∧ R p.2 q.2) := by
  rw [strength_l, strength_l]
  apply Rcoupl_dmap
  exact Rcoupl_mono _ _ _ _ Hcpl fun _ _ h => ⟨rfl, rfl, h⟩

end Rcoupl_strength

/-! ## Refinement couplings -/

section refcoupl

/-- Rocq: `is_refcoupl`. -/
def is_refcoupl (μ1 : Distr α) (μ2 : Distr β) (μ : Distr (α × β)) : Prop :=
  lmarg μ = μ1 ∧ ∀ b : β, rmarg μ b ≤ μ2 b

/-- Rocq: `ex_refcoupl`. -/
def ex_refcoupl (μ1 : Distr α) (μ2 : Distr β) : Prop :=
  ∃ μ : Distr (α × β), is_refcoupl μ1 μ2 μ

end refcoupl

section refRcoupl

/-- Rocq: `is_refRcoupl`. -/
def is_refRcoupl (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) (μ : Distr (α × β)) : Prop :=
  is_refcoupl μ1 μ2 μ ∧ ∀ p : α × β, 0 < μ p → R p.1 p.2

/-- Rocq: `refRcoupl`. -/
def refRcoupl (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) : Prop :=
  ∃ μ : Distr (α × β), is_refRcoupl μ1 μ2 R μ

end refRcoupl

/-- Rocq: `is_refcoupl_dret`. -/
theorem is_refcoupl_dret (a : α) (b : β) : is_refcoupl (dret a) (dret b) (dret (a, b)) :=
  ⟨(is_coupl_dret a b).1, fun b' => by rw [(is_coupl_dret a b).2]⟩

section is_refRcoupl

variable (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop) (μ : Distr (α × β))

/-- Rocq: `is_refRcoupl_mass_l`. -/
theorem is_refRcoupl_mass_l (h : is_refRcoupl μ1 μ2 R μ) : ∑' p, μ p = ∑' a, μ1 a := by
  rw [← h.1.1, lmarg, dmap_mass]

/-- Rocq: `is_refRcoupl_mass_r`. -/
theorem is_refRcoupl_mass_r (h : is_refRcoupl μ1 μ2 R μ) : ∑' p, μ p ≤ ∑' b, μ2 b := by
  rw [← dmap_mass μ Prod.snd]
  exact ENNReal.tsum_le_tsum h.1.2

/-- Rocq: `is_refRcoupl_mass_eq`. -/
theorem is_refRcoupl_mass_eq (h : is_refRcoupl μ1 μ2 R μ) : ∑' a, μ1 a ≤ ∑' b, μ2 b := by
  rw [← is_refRcoupl_mass_l μ1 μ2 R μ h]
  exact is_refRcoupl_mass_r μ1 μ2 R μ h

end is_refRcoupl

section refRcoupl

/-- Rocq: `refRcoupl_mass_eq`. -/
theorem refRcoupl_mass_eq (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop)
    (h : refRcoupl μ1 μ2 R) : ∑' a, μ1 a ≤ ∑' b, μ2 b := by
  obtain ⟨μ, hμ⟩ := h
  exact is_refRcoupl_mass_eq μ1 μ2 R μ hμ

/-- Rocq: `refRcoupl_eq_elim`. -/
theorem refRcoupl_eq_elim (μ1 μ2 : Distr α) (h : refRcoupl μ1 μ2 (· = ·)) :
    ∀ a, μ1 a ≤ μ2 a := by
  obtain ⟨μ, ⟨hL, hR⟩, HμS⟩ := h
  intro a
  refine le_trans ?_ (hR a)
  rw [← hL, lmarg_pmf, rmarg_pmf]
  refine ENNReal.tsum_le_tsum fun b => ?_
  by_cases hab : a = b
  · subst hab; exact le_rfl
  · rw [pmf_eq_0_not_gt_0 μ (a, b) fun hp => hab (HμS _ hp)]
    exact zero_le

/-- Rocq: `refRcoupl_from_leq`. -/
theorem refRcoupl_from_leq (μ1 μ2 : Distr α) (Hleq : ∀ a, μ1 a ≤ μ2 a) :
    refRcoupl μ1 μ2 (· = ·) := by
  classical
  refine ⟨ddiag μ1, ⟨ddiag_lmarg μ1, fun a => by rw [ddiag_rmarg]; exact Hleq a⟩,
    fun p hp => ?_⟩
  rw [ddiag_pmf] at hp
  by_contra hne
  simp [hne] at hp

/-- Rocq: `refRcoupl_eq_refl`. -/
theorem refRcoupl_eq_refl (μ1 : Distr α) : refRcoupl μ1 μ1 (· = ·) :=
  refRcoupl_from_leq μ1 μ1 fun _ => le_rfl

/-- Rocq: `refRcoupl_eq_trans`. -/
theorem refRcoupl_eq_trans (μ1 μ2 μ3 : Distr α) (H12 : refRcoupl μ1 μ2 (· = ·))
    (H23 : refRcoupl μ2 μ3 (· = ·)) : refRcoupl μ1 μ3 (· = ·) :=
  refRcoupl_from_leq μ1 μ3 fun a =>
    (refRcoupl_eq_elim _ _ H12 a).trans (refRcoupl_eq_elim _ _ H23 a)

/-- Rocq: `refRcoupl_eq_refRcoupl_unfoldl`. -/
theorem refRcoupl_eq_refRcoupl_unfoldl (μ1 μ2 : Distr α) (μ3 : Distr β) (R : α → β → Prop)
    (h12 : Rcoupl μ1 μ2 (· = ·)) (h23 : refRcoupl μ2 μ3 R) : refRcoupl μ1 μ3 R := by
  rw [Rcoupl_eq_elim μ1 μ2 h12]; exact h23

/-- Rocq: `refRcoupl_eq_refRcoupl_unfoldr`. -/
theorem refRcoupl_eq_refRcoupl_unfoldr (μ1 : Distr α) (μ2 μ3 : Distr β) (R : α → β → Prop)
    (h12 : refRcoupl μ1 μ2 R) (h23 : Rcoupl μ2 μ3 (· = ·)) : refRcoupl μ1 μ3 R := by
  rw [← Rcoupl_eq_elim μ2 μ3 h23]; exact h12

/-- Rocq: `Rcoupl_refRcoupl`. -/
theorem Rcoupl_refRcoupl (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop)
    (h : Rcoupl μ1 μ2 R) : refRcoupl μ1 μ2 R := by
  obtain ⟨μ, ⟨hL, hR⟩, HμS⟩ := h
  exact ⟨μ, ⟨hL, fun b => by rw [hR]⟩, HμS⟩

/-- Rocq: `Rcoupl_refRcoupl'`. -/
theorem Rcoupl_refRcoupl' (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop)
    (h : Rcoupl μ1 μ2 R) : refRcoupl μ2 μ1 (flip R) :=
  Rcoupl_refRcoupl _ _ _ (Rcoupl_swap _ _ _ h)

/-- Rocq: `refRcoupl_dret`. -/
theorem refRcoupl_dret (a : α) (b : β) (R : α → β → Prop) (h : R a b) :
    refRcoupl (dret a) (dret b) R := by
  refine ⟨_, is_refcoupl_dret a b, fun p hp => ?_⟩
  rw [dret_pos _ _ hp]; exact h

/-- Rocq: `refRcoupl_dbind`. -/
theorem refRcoupl_dbind (f : α → Distr α') (g : β → Distr β') (μ1 : Distr α) (μ2 : Distr β)
    (R : α → β → Prop) (S : α' → β' → Prop)
    (Hfg : ∀ a b, R a b → refRcoupl (f a) (g b) S) (Hμ : refRcoupl μ1 μ2 R) :
    refRcoupl (μ1 ≫= f) (μ2 ≫= g) S := by
  obtain ⟨μ, ⟨hL, hR⟩, HμS⟩ := Hμ
  have Hfg' : ∀ p : α × β, ∃ μ' : Distr (α' × β'),
      R p.1 p.2 → is_refRcoupl (f p.1) (g p.2) S μ' := by
    intro p
    by_cases hR : R p.1 p.2
    · obtain ⟨μ', hμ'⟩ := Hfg _ _ hR
      exact ⟨μ', fun _ => hμ'⟩
    · exact ⟨dzero, fun h => absurd h hR⟩
  choose Ch HCh using Hfg'
  refine ⟨μ ≫= Ch, ⟨?_, ?_⟩, ?_⟩
  · rw [lmarg_dbind, dbind_eq _ (fun p => f p.1) μ μ
      (fun p hp => (HCh p (HμS p hp)).1.1) (fun _ => rfl), dbind_fst, hL]
  · intro b'
    rw [rmarg_dbind]
    calc (μ ≫= fun p => rmarg (Ch p)) b' ≤ (μ ≫= fun p => g p.2) b' := by
          refine ENNReal.tsum_le_tsum fun p => ?_
          by_cases hp : μ p = 0
          · simp [hp]
          · exact mul_le_mul_right ((HCh p (HμS p (pos_iff_ne_zero.2 hp))).1.2 b') _
      _ = (rmarg μ ≫= g) b' := by rw [dbind_snd]
      _ ≤ (μ2 ≫= g) b' := distr_le_dbind _ _ _ _ hR (fun _ => distr_le_refl _) b'
  · intro q hq
    obtain ⟨p, hq', hp⟩ := (dbind_pos _ _ _).1 hq
    exact (HCh p (HμS p hp)).2 q hq'

/-- Rocq: `refRcoupl_dzero`. -/
theorem refRcoupl_dzero (μ : Distr β) (R : α → β → Prop) : refRcoupl (dzero : Distr α) μ R :=
  ⟨dzero, ⟨lmarg_dzero, fun b => by rw [rmarg_dzero, dzero_0]; exact zero_le⟩,
    fun p hp => absurd hp (dzero_supp_empty p)⟩

/-- Rocq: `refRcoupl_mono`. -/
theorem refRcoupl_mono (μ1 : Distr α) (μ2 : Distr β) (R S : α → β → Prop)
    (Hwk : ∀ a b, R a b → S a b) (h : refRcoupl μ1 μ2 R) : refRcoupl μ1 μ2 S := by
  obtain ⟨μ, hμ, HμS⟩ := h
  exact ⟨μ, hμ, fun p hp => Hwk _ _ (HμS p hp)⟩

/-- Rocq: `refRcoupl_trivial`. -/
theorem refRcoupl_trivial (μ1 : Distr α) (μ2 : Distr β) (Hμ : ∑' a, μ1 a ≤ ∑' b, μ2 b) :
    refRcoupl μ1 μ2 (fun _ _ => True) := by
  by_cases h1 : ∑' a, μ1 a = 0
  · rw [SeriesC_zero_dzero μ1 h1]; exact refRcoupl_dzero μ2 _
  have h2 : ∑' b, μ2 b ≠ 0 := fun h => h1 (le_antisymm (h ▸ Hμ) zero_le)
  have h2t : ∑' b, μ2 b ≠ ∞ := SeriesC_ne_top μ2
  have hcancel : (∑' b, μ2 b)⁻¹ * ∑' b, μ2 b = 1 := ENNReal.inv_mul_cancel h2 h2t
  have hle : (∑' b, μ2 b)⁻¹ * ∑' a, μ1 a ≤ 1 := by
    calc (∑' b, μ2 b)⁻¹ * ∑' a, μ1 a ≤ (∑' b, μ2 b)⁻¹ * ∑' b, μ2 b := by gcongr
      _ = 1 := hcancel
  have Hle1 : (∑' b, μ2 b)⁻¹ * ∑' p, dprod μ1 μ2 p ≤ 1 := by
    rw [dprod_mass, mul_comm (∑' a, μ1 a), ← mul_assoc, hcancel, one_mul]
    exact μ1.mass_le_one
  refine ⟨distr_scal _ (dprod μ1 μ2) Hle1, ⟨?_, fun b => ?_⟩, fun _ _ => trivial⟩
  · ext a
    rw [lmarg_pmf]
    change ∑' b, (∑' b, μ2 b)⁻¹ * dprod μ1 μ2 (a, b) = μ1 a
    simp_rw [dprod_pmf]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, mul_comm, mul_assoc,
      mul_comm (∑' b, μ2 b), hcancel, mul_one]
  · rw [rmarg_pmf]
    change ∑' a, (∑' b, μ2 b)⁻¹ * dprod μ1 μ2 (a, b) ≤ μ2 b
    simp_rw [dprod_pmf]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    calc (∑' b, μ2 b)⁻¹ * ((∑' a, μ1 a) * μ2 b) = μ2 b * ((∑' b, μ2 b)⁻¹ * ∑' a, μ1 a) := by
          ring
      _ ≤ μ2 b * 1 := mul_le_mul_right hle _
      _ = μ2 b := mul_one _

/-- Rocq: `refRcoupl_pos_R`. -/
theorem refRcoupl_pos_R (μ1 : Distr α) (μ2 : Distr β) (R : α → β → Prop)
    (h : refRcoupl μ1 μ2 R) :
    refRcoupl μ1 μ2 (fun a' b' => R a' b' ∧ 0 < μ1 a' ∧ 0 < μ2 b') := by
  obtain ⟨μ, ⟨hL, hR⟩, HR⟩ := h
  refine ⟨μ, ⟨hL, hR⟩, ?_⟩
  rintro ⟨a, b⟩ hp
  refine ⟨HR _ hp, ?_, ?_⟩
  · rw [← hL]; exact lmarg_pos_of_pos μ a b hp
  · exact lt_of_lt_of_le (rmarg_pos_of_pos μ a b hp) (hR b)

/-- Rocq: `refRcoupl_dret_trivial`. -/
theorem refRcoupl_dret_trivial (μ : Distr α) (b : β) :
    refRcoupl μ (dret b) (fun _ _ => True) := by
  apply refRcoupl_trivial
  rw [dret_mass]; exact μ.mass_le_one

/-- Rocq: `refRcoupl_dret_r_inv`. -/
theorem refRcoupl_dret_r_inv (μ1 : Distr α) (b : β) (R : α → β → Prop)
    (h : refRcoupl μ1 (dret b) R) : refRcoupl μ1 (dret b) (fun a' b' => R a' b' ∧ b = b') :=
  refRcoupl_mono _ _ _ _ (fun _ _ h' => ⟨h'.1, (dret_pos _ _ h'.2.2).symm⟩)
    (refRcoupl_pos_R _ _ _ h)

/-- Rocq: `refRcoupl_dret_l_inv`. -/
theorem refRcoupl_dret_l_inv (μ2 : Distr β) (a : α) (R : α → β → Prop)
    (h : refRcoupl (dret a) μ2 R) :
    refRcoupl (dret a) μ2 (fun a' b' => R a' b' ∧ a' = a ∧ 0 < μ2 b') :=
  refRcoupl_mono _ _ _ _ (fun _ _ h' => ⟨h'.1, dret_pos _ _ h'.2.1, h'.2.2⟩)
    (refRcoupl_pos_R _ _ _ h)

end refRcoupl

/-- Rocq: notation `μ1 ≾ μ2 : R` for `refRcoupl μ1 μ2 R`. -/
scoped notation:100 μ1:101 " ≾ " μ2:101 " : " R:200 => refRcoupl μ1 μ2 R

/-- Rocq: notation `μ1 ≿ μ2 : R` for `refRcoupl μ2 μ1 (flip R)`. -/
scoped notation:100 μ1:101 " ≿ " μ2:101 " : " R:200 => refRcoupl μ2 μ1 (flip R)

end Prob

end
