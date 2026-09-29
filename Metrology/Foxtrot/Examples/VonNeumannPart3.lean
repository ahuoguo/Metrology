module

public import Metrology.Foxtrot.Examples.VonNeumann

/-!
# The von Neumann trick: from a fair coin to the concurrent von Neumann program

Ported from clutch/theories/foxtrot/examples/von_neumann.v (part 3: `wp_rand_prog_rand_prog'`,
`wp_rand_prog'_von_neumann_con_prog`).

## Rocq → Lean map
* `wp_rand_prog_rand_prog'`, `wp_rand_prog'_von_neumann_con_prog`: same names.
* `ec_ind_simpl` is iris-lean's `ErrorCredit.Induction.simple` (amplification factor in `ℝ≥0`).
  Rocq's real `k = ((N+2)*(N+2))%nat / ((N+2)*(N+2) - 2*(N+1))%nat` is `vn_k N : ℝ≥0`, whose
  `ℝ≥0∞` cast is the factor `((N+1+1)*(N+1+1) : ℕ) / ((N+1+1)*(N+1+1) - 2 * (N+1) : ℕ)` of
  `pupd_couple_von_neumann_2` (`vn_k_coe`; the length of the lists is `N + 1`).
* The lists `(λ x, (0, x)) <$> seq 1 (S N)` and `(λ x, (x, 0)) <$> seq 1 (S N)` are
  `vn2_l1 N` and `vn2_l2 N` (`seq` is `List.range'`); their side conditions (proved inline in
  Rocq) are the lemmas `mem_vn2_l1`, `mem_vn2_l2`, `vn2_l1_bound`, `vn2_l2_bound`,
  `vn2_nodup`, `vn2_len`, `vn2_len_eq`.

## Deviations
* The natural-number subtraction of the factor is truncated as in Rocq; the denominator is
  `(N+2)^2 - 2(N+1) = N^2 + 2N + 2 > 0`, so `x / 0 = ∞` never applies (`vn_k_one_lt`).
* Rocq's `iRevert "Hspec Hα"; iApply (ec_ind_simpl _ k with "[][$]")` applies
  `ErrorCredit.Induction.simple` with the proposition `P` given explicitly. The invariant
  `l ↦ₛ #0` is allocated before `rand_prog'`'s closure is returned, so it is in the persistent
  context of the induction.
* Rocq's `iMod (pupd_fork with "[$]") as "[Hspec _]"` is `tp_fork j as j' -`.
* In the rejected case, Rocq's `ec_eq` (the amplified error `k * ε` written with `N+2` and
  `2 * (N+1)` against the `S N * S N`-shaped factor of the rule) is `ErrorCredit.ext` with
  `vn_k_coe`.

## Added
* `vn_k`, `vn_k_coe`, `vn_k_one_lt`, `vn2_l1`, `vn2_l2` and the list lemmas above.

## Omitted
None.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot Foxtrot.BinaryRel Foxtrot.Lib.Spawn Foxtrot.Lib.Par Foxtrot.Lib.Min
open Foxtrot.Lib.Conversion

namespace Foxtrot.Examples.VonNeumann

/-! ## The factor and the lists of `pupd_couple_von_neumann_2` -/

section helpers

variable (N : ℕ)

/-- Added: Rocq's real `k = ((N+2)*(N+2))%nat / ((N+2)*(N+2) - 2 * (N+1))%nat` as an `ℝ≥0`
(the factor of `ec_ind_simpl`). -/
def vn_k : ℝ≥0 :=
  (((N + 1 + 1) * (N + 1 + 1) : ℕ) : ℝ≥0) / (((N + 1 + 1) * (N + 1 + 1) - 2 * (N + 1) : ℕ) : ℝ≥0)

theorem vn_k_den_pos : 0 < (N + 1 + 1) * (N + 1 + 1) - 2 * (N + 1) := by
  have : 2 * (N + 1) < (N + 1 + 1) * (N + 1 + 1) := by nlinarith
  omega

/-- Added: the `ℝ≥0∞` cast of `vn_k`. -/
theorem vn_k_coe :
    ((vn_k N : ℝ≥0) : ℝ≥0∞) = (((N + 1 + 1) * (N + 1 + 1) : ℕ) : ℝ≥0∞) /
      (((N + 1 + 1) * (N + 1 + 1) - 2 * (N + 1) : ℕ) : ℝ≥0∞) := by
  rw [vn_k, ENNReal.coe_div (Nat.cast_ne_zero.mpr (vn_k_den_pos N).ne')]
  simp only [ENNReal.coe_natCast]

/-- Added (Rocq: the inline `Rcomplements.Rlt_div_r` proof): `1 < vn_k`. -/
theorem vn_k_one_lt : 1 < vn_k N := by
  rw [vn_k, one_lt_div (by exact_mod_cast vn_k_den_pos N)]
  exact_mod_cast (by have := vn_k_den_pos N; omega :
    (N + 1 + 1) * (N + 1 + 1) - 2 * (N + 1) < (N + 1 + 1) * (N + 1 + 1))

/-- Rocq: `(λ x, (0, x)%nat) <$> lis` with `lis = seq 1 (S N)`. -/
def vn2_l1 : List (ℕ × ℕ) := (List.range' 1 (N + 1)).map (fun x => (0, x))

/-- Rocq: `(λ x, (x, 0)%nat) <$> lis`. -/
def vn2_l2 : List (ℕ × ℕ) := (List.range' 1 (N + 1)).map (fun x => (x, 0))

variable {N}

theorem mem_vn2_l1 (a b : ℕ) : (a, b) ∈ vn2_l1 N ↔ a = 0 ∧ 1 ≤ b ∧ b ≤ N + 1 := by
  simp only [vn2_l1, List.mem_map, List.mem_range', Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl, rfl⟩
    omega
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨b, ⟨b - 1, by omega, by omega⟩, rfl, rfl⟩

theorem mem_vn2_l2 (a b : ℕ) : (a, b) ∈ vn2_l2 N ↔ 1 ≤ a ∧ a ≤ N + 1 ∧ b = 0 := by
  simp only [vn2_l2, List.mem_map, List.mem_range', Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl, rfl⟩
    omega
  · rintro ⟨h1, h2, rfl⟩
    exact ⟨a, ⟨a - 1, by omega, by omega⟩, rfl, rfl⟩

theorem vn2_l1_bound : ∀ x ∈ vn2_l1 N, x.1 ≤ N + 1 ∧ x.2 ≤ N + 1 := by
  rintro ⟨a, b⟩ h
  rw [mem_vn2_l1] at h
  simp only
  omega

theorem vn2_l2_bound : ∀ x ∈ vn2_l2 N, x.1 ≤ N + 1 ∧ x.2 ≤ N + 1 := by
  rintro ⟨a, b⟩ h
  rw [mem_vn2_l2] at h
  simp only
  omega

theorem vn2_nodup : (vn2_l1 N ++ vn2_l2 N).Nodup := by
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (List.nodup_range' ..).map (fun x y h => by simpa using h)
  · exact (List.nodup_range' ..).map (fun x y h => by simpa using h)
  · rintro ⟨a, b⟩ h1 ⟨a', b'⟩ h2 heq
    rw [mem_vn2_l1] at h1
    rw [mem_vn2_l2] at h2
    simp only [Prod.mk.injEq] at heq
    omega

theorem vn2_len_eq : (vn2_l1 N).length = N + 1 := by
  simp [vn2_l1]

theorem vn2_len : (vn2_l1 N).length = (vn2_l2 N).length := by
  simp [vn2_l1, vn2_l2]

theorem vn2_len_bound : 2 * (vn2_l1 N).length < (N + 1 + 1) * (N + 1 + 1) := by
  rw [vn2_len_eq]
  nlinarith

end helpers

section proof'

variable (N : ℕ) (ad : val)
variable {GF : BundledGFunctors} [foxtrotRGS GF] [spawnG GF]

set_option linter.unusedSectionVars false in
/-- Rocq: `wp_rand_prog_rand_prog'`. -/
theorem wp_rand_prog_rand_prog' (_Ht : Htyped ad) (K : List ectx_item) (j : ℕ) :
    ⊢ j ⤇ fill K cpl(&rand_prog' &ad) -∗
      WP cpl(&rand_prog &ad)
        {{ v, ∃ v' : val, j ⤇ fill K (Val v') ∗
          (lrel_arr lrel_unit lrel_bool : lrel GF) v v' }} := by
  iintro Hspec
  unfold rand_prog' rand_prog flip flipL
  tp_pures j
  wp_pures
  iexists _
  iframe Hspec
  imodintro
  dsimp only [lrel_arr, lrel_unit]
  imodintro
  iintro %v1 %v2 %⟨h1, h2⟩
  subst h1 h2
  unfold BinaryRel.refines BinaryRel.refines_def
  iintro %K' %j' Hspec
  wp_pures
  tp_pures j'
  tp_allocnattape j' α as Hα
  tp_pures j'
  tp_bind j' (Rand _ _)
  wp_bind (Rand _ _)
  wp_apply wp_couple_rand_rand_lbl 1 id Function.bijective_id ((1 : ℕ) : ℤ) _ α j'
    (by simp) (fun n hn => hn) $$ [Hα Hspec] with %n ⟨-, Hspec, %Hn⟩
  · iframe Hα Hspec
  simp only [id]
  rw [fill_app_rctx _ _ (Val (LitV (LitInt (n : ℤ))))]
  imod spec_int_to_bool ⊤ j' K' (n : ℤ) $$ Hspec with Hspec
  wp_apply wp_int_to_bool (n : ℤ) ⊤ $$ []
  · itrivial
  iintro -
  iexists _
  iframe Hspec
  dsimp only [lrel_bool]
  iexists _
  ipureintro
  exact ⟨rfl, rfl⟩

set_option linter.unusedSectionVars false in
/-- Rocq: `wp_rand_prog'_von_neumann_con_prog`. -/
theorem wp_rand_prog'_von_neumann_con_prog (_Ht : Htyped ad) (K : List ectx_item) (j : ℕ) :
    ⊢ j ⤇ fill K cpl(&(von_neumann_con_prog N) &ad) -∗
      WP cpl(&rand_prog' &ad)
        {{ v, ∃ v' : val, j ⤇ fill K (Val v') ∗
          (lrel_arr lrel_unit lrel_bool : lrel GF) v v' }} := by
  iintro Hspec
  unfold rand_prog' von_neumann_con_prog flipL
  tp_pures j
  tp_alloc j as l Hl
  tp_pures j
  tp_fork j as j'' -
  tp_pures j
  imod inv_alloc nroot ⊤ iprop(l ↦ₛ LitV (LitInt 0)) $$ [Hl] with #Hinv
  · inext
    iexact Hl
  wp_pures
  iexists _
  iframe Hspec
  imodintro
  dsimp only [lrel_arr, lrel_unit]
  imodintro
  iintro %v1 %v2 %⟨h1, h2⟩
  subst h1 h2
  unfold BinaryRel.refines BinaryRel.refines_def
  iintro %K' %j' Hspec
  wp_pures
  wp_alloctape α as Hα
  wp_pures
  imod pupd_epsilon_err ⊤ with ⟨%ε, %Hε, Herr⟩
  irevert Hspec Hα
  iapply ErrorCredit.Induction.simple Hε (vn_k_one_lt N) $$ [] Herr
  imodintro
  iintro ⟨Hind, Herr⟩ Hspec Hα
  tp_pures j'
  iapply pupd_wp
  iinv Hinv with >Hl Hclose
  tp_load j'
  imod Hclose $$ Hl
  imodintro
  tp_bind j' (App (App (Val min_prog) _) _)
  imod spec_min_prog ⊤ j' _ 0 (N : ℤ) $$ Hspec with Hspec
  rw [min_eq_left (by omega : (0 : ℤ) ≤ N)]
  tp_pure j'
  tp_pure j'
  tp_bind j' (App (App (Val par) _) _)
  imod tp_par $$ Hspec with ⟨%j1, %j2, %K1, %K2, Hspec1, Hspec2, Hcont⟩
  tp_bind j1 (Rand _ _)
  tp_bind j2 (Rand _ _)
  imod pupd_couple_von_neumann_2 (N := N + 1) (vn2_l1 N) (vn2_l2 N) α [] j1 _ j2 _ ⊤ ε
      vn2_l1_bound vn2_l2_bound vn2_nodup vn2_len (by rw [vn2_len_eq]; omega) vn2_len_bound Hε
      $$ Hspec1 Hspec2 [Hα] Herr with ⟨%x, %y, %Hx, %Hy, Hspec1, Hspec2, Hα⟩
  · inext
    iexact Hα
  rw [vn2_len_eq]
  by_cases C1 : (x, y) ∈ vn2_l1 N
  · simp only [C1, ↓reduceIte]
    rw [mem_vn2_l1] at C1
    obtain ⟨rfl, C1, -⟩ := C1
    tp_pures j1
    tp_pures j2
    rw [decide_eq_false (by omega : ¬ y = 0)]
    imod Hcont $$ %_ %_ %⊤ [Hspec1 Hspec2] with Hspec
    · iframe Hspec1 Hspec2
    tp_pures j'
    simp only [List.nil_append]
    wp_randtape
    wp_apply wp_int_to_bool 1 ⊤ $$ []
    · itrivial
    iintro -
    rw [Z_to_bool_neq_0 1 (by decide)]
    iexists _
    iframe Hspec
    dsimp only [lrel_bool]
    iexists true
    ipureintro
    exact ⟨rfl, rfl⟩
  by_cases C2 : (x, y) ∈ vn2_l2 N
  · simp only [C1, C2, ↓reduceIte]
    rw [mem_vn2_l2] at C2
    obtain ⟨C2, -, rfl⟩ := C2
    tp_pures j1
    tp_pures j2
    rw [decide_eq_false (by omega : ¬ x = 0)]
    imod Hcont $$ %_ %_ %⊤ [Hspec1 Hspec2] with Hspec
    · iframe Hspec1 Hspec2
    tp_pures j'
    simp only [List.nil_append]
    wp_randtape
    wp_apply wp_int_to_bool 0 ⊤ $$ []
    · itrivial
    iintro -
    rw [Z_to_bool_eq_0]
    iexists _
    iframe Hspec
    dsimp only [lrel_bool]
    iexists false
    ipureintro
    exact ⟨rfl, rfl⟩
  simp only [C1, C2, ↓reduceIte]
  rw [mem_vn2_l1] at C1
  rw [mem_vn2_l2] at C2
  tp_pures j1
  tp_pures j2
  icases Hα with ⟨Hα, Herr⟩
  by_cases C3 : x = 0
  · rw [decide_eq_true C3, decide_eq_true (by omega : y = 0)]
    imod Hcont $$ %_ %_ %⊤ [Hspec1 Hspec2] with Hspec
    · iframe Hspec1 Hspec2
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    iapply Hind $$ [Herr] Hspec Hα
    iapply ErrorCredit.ext (by rw [vn_k_coe]) $$ Herr
  · rw [decide_eq_false C3, decide_eq_false (by omega : ¬ y = 0)]
    imod Hcont $$ %_ %_ %⊤ [Hspec1 Hspec2] with Hspec
    · iframe Hspec1 Hspec2
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    tp_pure j'
    iapply Hind $$ [Herr] Hspec Hα
    iapply ErrorCredit.ext (by rw [vn_k_coe]) $$ Herr

end proof'

end Foxtrot.Examples.VonNeumann
