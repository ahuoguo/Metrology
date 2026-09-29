module

public import Metrology.Coneris.Lib.HocapRandAlt

/-!
# An alternative hocap rand spec, part 2: simulating a rand 3 with two flips

Ported from clutch/theories/coneris/lib/hocap_rand_alt.v (section `impl2`).

## Rocq → Lean mapping
* `rand_inv_pred2`, `is_rand2`, `expander`, `rand_tapes2`, `rand_token2`, `rand_spec2` (Rocq:
  `#[local] Program Definition`, a definition here); the `Next Obligation`s are the helper
  theorems `rand_spec2_*`. `l ≫= (λ x, [x/2; x mod 2])` is
  `l.flatMap fun x => [x / 2, x % 2]`.
* `rand_inv_pred2 γ` is `rand_inv_pred_gen 1 γ` (see `Coneris.Lib.HocapRandAlt`).

## Proofs that differ from Rocq
* `rand_tapes_presample`: Rocq presamples the first bit `n1` with the error function
  `1/2 * (if n1 = 1 then ε2 2 + ε2 3 else ε2 0 + ε2 1)` and then, by cases on `n1`, the second
  bit `n2` with `if n2 = 1 then ε2 3 else ε2 2` (resp. `ε2 1`/`ε2 0`). Here both cases are one:
  the first error function is `1/2 * (ε2 (2 n1) + ε2 (2 n1 + 1))` (the helper `flip_err1`) and
  the second one is `ε2 (2 n1 + n2)` (the same functions as in Rocq, written uniformly); the
  sampled value is `2 n1 + n2`. The series inequalities are the helpers `flip_err1_sum` and
  `flip_err2_sum`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris.Lib.AbstractTape

namespace Coneris.Lib.HocapRandAlt

/-! ## Error functions of the two presampling steps (pure helpers) -/

/-- Helper: the value `2 n1 + n2` of the two bits `n1`, `n2`. -/
def flip_val (n1 n2 : Fin (1 + 1)) : Fin (3 + 1) := ⟨2 * n1 + n2, by omega⟩

/-- Helper: the error function of the first presampling step of `rand_spec2`. -/
def flip_err1 (ε2 : Fin (3 + 1) → ℝ≥0∞) (n1 : Fin (1 + 1)) : ℝ≥0∞ :=
  1 / 2 * (ε2 (flip_val n1 0) + ε2 (flip_val n1 1))

theorem flip_err1_sum (ε : ℝ≥0∞) (ε2 : Fin (3 + 1) → ℝ≥0∞)
    (Hsum : ∑' n, 1 / (((3 : ℕ) : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ∑' n1, 1 / (((1 : ℕ) : ℝ≥0∞) + 1) * flip_err1 ε2 n1 ≤ ε := by
  refine le_trans (le_of_eq ?_) Hsum
  rw [tsum_fintype, tsum_fintype, Fin.sum_univ_two, Fin.sum_univ_four]
  have h4 : (1 : ℝ≥0∞) / (((3 : ℕ) : ℝ≥0∞) + 1) = 1 / 2 * (1 / 2) := by
    rw [one_div, one_div, ← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  have h2 : (1 : ℝ≥0∞) / (((1 : ℕ) : ℝ≥0∞) + 1) = 1 / 2 := by norm_num
  simp only [flip_err1, h4, h2]
  have e0 : flip_val 0 0 = 0 := rfl
  have e1 : flip_val 0 1 = 1 := rfl
  have e2 : flip_val 1 0 = 2 := rfl
  have e3 : flip_val 1 1 = 3 := rfl
  rw [e0, e1, e2, e3]
  ring

/-- Helper: the series inequality of the second presampling step of `rand_spec2`. -/
theorem flip_err2_sum (ε2 : Fin (3 + 1) → ℝ≥0∞) (n1 : Fin (1 + 1)) :
    ∑' n2, 1 / (((1 : ℕ) : ℝ≥0∞) + 1) * ε2 (flip_val n1 n2) ≤ flip_err1 ε2 n1 := by
  rw [tsum_fintype, Fin.sum_univ_two, flip_err1, mul_add]
  norm_num

/-! ## Implementation 2 -/

section impl2

variable {GF : BundledGFunctors} [conerisGS GF] [GhostMapG GF val Unit val_map]
  [abstract_tapesGS GF]

/-- Rocq: `rand_inv_pred2`. -/
def rand_inv_pred2 (γ : GName × GName) : IProp GF := rand_inv_pred_gen 1 γ

/-- Rocq: `is_rand2`. -/
def is_rand2 (N : Namespace) (γ : GName × GName) : IProp GF := inv N (rand_inv_pred2 γ)

/-- Rocq: `expander`. -/
def expander (l : List ℕ) : List ℕ := l.flatMap fun x => [x / 2, x % 2]

/-- Rocq: `rand_tapes2`. -/
def rand_tapes2 (α : val) (ns : List ℕ) (γ : GName × GName) : IProp GF :=
  iprop((α ◯↪N (1; expander ns) @ γ.2) ∗ ⌜∀ x ∈ ns, x ≤ 3⌝)

/-- Rocq: `rand_token2`. -/
def rand_token2 (α : val) (γ : GName × GName) : IProp GF :=
  ghost_map_elem (H := val_map) γ.1 (DFrac.own 1) α ()

/-- Rocq: `rand_allocate_tape` of `rand_spec2`. -/
def rand_allocate_tape2 : val := cpl_val(λ <>, alloc(#1))

/-- Rocq: `rand_tape` of `rand_spec2`. -/
def rand_tape2 : val := cpl_val(λ α, (rand(α) #1) + (#2 * rand(α) #1))

instance is_rand2_persistent (N : Namespace) (γ : GName × GName) :
    Persistent (is_rand2 (GF := GF) N γ) := by
  unfold is_rand2; infer_instance

instance rand_tapes2_timeless (α : val) (ns : List ℕ) (γ : GName × GName) :
    Timeless (rand_tapes2 (GF := GF) α ns γ) := by
  unfold rand_tapes2; infer_instance

instance rand_token2_timeless (α : val) (γ : GName × GName) :
    Timeless (rand_token2 (GF := GF) α γ) := by
  unfold rand_token2; infer_instance

omit [conerisGS GF] [GhostMapG GF val Unit val_map] in
/-- Rocq: first `Next Obligation` of `rand_spec2`. -/
theorem rand_spec2_rand_tapes_exclusive (α : val) (ns ns' : List ℕ) (γ : GName × GName) :
    ⊢@{IProp GF} rand_tapes2 α ns γ -∗ rand_tapes2 α ns' γ -∗ False := by
  unfold rand_tapes2
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply abstract_tapes_frag_exclusive $$ H1 H2

omit [conerisGS GF] [abstract_tapesGS GF] in
/-- Rocq: second `Next Obligation` of `rand_spec2`. -/
theorem rand_spec2_rand_token_exclusive (α : val) (γ : GName × GName) :
    ⊢@{IProp GF} rand_token2 α γ -∗ rand_token2 α γ -∗ False :=
  rand_token_gen_exclusive α γ.1

omit [conerisGS GF] [GhostMapG GF val Unit val_map] in
/-- Rocq: third `Next Obligation` of `rand_spec2`. -/
theorem rand_spec2_rand_tapes_valid (α : val) (ns : List ℕ) (γ : GName × GName) :
    ⊢@{IProp GF} rand_tapes2 α ns γ -∗ ⌜∀ n ∈ ns, n ≤ 3⌝ := by
  unfold rand_tapes2
  iintro ⟨-, %H⟩
  ipureintro
  exact H

/-- Rocq: fourth `Next Obligation` of `rand_spec2`. -/
theorem rand_spec2_rand_tapes_presample (N : Namespace) (E : CoPset) (α : val) (ns : List ℕ)
    (ε : ℝ≥0∞) (ε2 : Fin (3 + 1) → ℝ≥0∞) (γ : GName × GName) (HN : ↑N ⊆ E)
    (Hsum : ∑' n, 1 / (((3 : ℕ) : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢@{IProp GF} is_rand2 N γ -∗ rand_tapes2 α ns γ -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (3 + 1), ↯ (ε2 n) ∗ rand_tapes2 α (ns ++ [(n : ℕ)]) γ) := by
  unfold is_rand2 rand_inv_pred2 rand_tapes2
  iintro #Hinv ⟨H1, %Hf⟩ Herr
  imod rand_inv_gen_presample 1 N E α _ ε (flip_err1 ε2) γ HN (flip_err1_sum ε ε2 Hsum)
    $$ Hinv H1 Herr with ⟨%n1, Herr, H1⟩
  imod rand_inv_gen_presample 1 N E α _ _ (fun n2 => ε2 (flip_val n1 n2)) γ HN
    (flip_err2_sum ε2 n1) $$ Hinv H1 Herr with ⟨%n2, Herr, H1⟩
  imodintro
  iexists flip_val n1 n2
  iframe Herr
  have hexp : expander (ns ++ [((flip_val n1 n2 : Fin (3 + 1)) : ℕ)]) =
      expander ns ++ [(n1 : ℕ)] ++ [(n2 : ℕ)] := by
    have h2lt := n2.isLt
    have h1 : (2 * (n1 : ℕ) + n2) / 2 = n1 := by omega
    have h2 : (2 * (n1 : ℕ) + n2) % 2 = n2 := by omega
    simp [expander, flip_val, h1, h2]
  rw [hexp]
  iframe H1
  ipureintro
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact Hf x hx
  · rw [List.mem_singleton.1 hx]
    exact Nat.lt_succ_iff.1 (flip_val n1 n2).isLt

/-- Rocq: fifth `Next Obligation` of `rand_spec2`. -/
theorem rand_spec2_rand_inv_create_spec (N : Namespace) (E : CoPset) (_HN : ↑N ⊆ E) :
    ⊢@{IProp GF} |={E}=> ∃ γ1, is_rand2 N γ1 :=
  rand_inv_gen_create 1 N E

/-- Rocq: sixth `Next Obligation` of `rand_spec2`. -/
theorem rand_spec2_rand_allocate_tape_spec (N : Namespace) (γ : GName × GName) (E : CoPset)
    (HN : ↑N ⊆ E) :
    {{ is_rand2 (GF := GF) N γ }} cpl(v(&rand_allocate_tape2) #()) @ E
    {{ v, RET v; rand_token2 v γ ∗ rand_tapes2 v [] γ }} := by
  unfold is_rand2 rand_inv_pred2
  iintro %Φ #Hinv HΦ
  wp_lam
  wp_apply rand_inv_gen_alloc 1 N γ E HN $$ Hinv with %v ⟨Htok, Hfrag⟩
  iapply HΦ
  unfold rand_token2 rand_tapes2
  simp only [expander, List.flatMap_nil]
  iframe Htok Hfrag
  ipureintro
  simp

/-- Rocq: seventh `Next Obligation` of `rand_spec2`. -/
theorem rand_spec2_rand_tape_spec_some (N : Namespace) (γ : GName × GName) (E : CoPset)
    (α : val) (n : ℕ) (ns : List ℕ) (HN : ↑N ⊆ E) :
    {{ is_rand2 (GF := GF) N γ ∗ rand_tapes2 α (n :: ns) γ }} cpl(v(&rand_tape2) v(&α)) @ E
    {{ RET LitV (LitInt (n : ℤ)); rand_tapes2 α ns γ }} := by
  unfold is_rand2 rand_inv_pred2 rand_tapes2
  iintro %Φ ⟨#Hinv, Hfrag, %H⟩ HΦ
  have hexp : expander (n :: ns) = n / 2 :: n % 2 :: expander ns := rfl
  rw [hexp]
  wp_lam
  wp_bind (Rand _ _)
  wp_apply rand_inv_gen_rand 1 N γ E α (n / 2) _ HN $$ [Hfrag] with Hfrag
  · iframe Hinv Hfrag
  wp_pures
  wp_bind (Rand _ _)
  wp_apply rand_inv_gen_rand 1 N γ E α (n % 2) _ HN $$ [Hfrag] with Hfrag
  · iframe Hinv Hfrag
  wp_pures
  have hn : n ≤ 3 := H n List.mem_cons_self
  have hval : (n : ℤ) % 2 + 2 * ((n : ℤ) / 2) = (n : ℤ) := by omega
  rw [hval]
  imodintro
  iapply HΦ
  iframe Hfrag
  ipureintro
  exact fun x hx => H x (List.mem_cons_of_mem n hx)

/-- Rocq: `rand_spec2` (a `#[local] Program Definition`). -/
@[instance_reducible]
def rand_spec2 : rand_spec' 3 GF where
  rand_allocate_tape := rand_allocate_tape2
  rand_tape := rand_tape2
  rand_tape_name := GName × GName
  is_rand := is_rand2
  rand_tapes := rand_tapes2
  rand_token := rand_token2
  is_rand_persistent := is_rand2_persistent
  rand_tapes_timeless := rand_tapes2_timeless
  rand_token_timeless := rand_token2_timeless
  rand_tapes_exclusive := rand_spec2_rand_tapes_exclusive
  rand_token_exclusive := rand_spec2_rand_token_exclusive
  rand_tapes_valid := rand_spec2_rand_tapes_valid
  rand_tapes_presample := rand_spec2_rand_tapes_presample
  rand_inv_create_spec := rand_spec2_rand_inv_create_spec
  rand_allocate_tape_spec := rand_spec2_rand_allocate_tape_spec
  rand_tape_spec_some := rand_spec2_rand_tape_spec_some

end impl2

end Coneris.Lib.HocapRandAlt
