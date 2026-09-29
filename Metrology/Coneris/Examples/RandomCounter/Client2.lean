module

public import Metrology.Coneris.Examples.RandomCounter.RandomCounter

/-!
# A sequential client of the random counter

Ported from clutch/theories/coneris/examples/random_counter/client2.v

The program increments a random counter twice with the same tape and returns
`4 * v + v'`, where `v` and `v'` are the two increments; the result is uniform on `fin 16`,
which is expressed by a presampling-style spec with an arbitrary error function
`ε2 : fin 16 → R`.

## Rocq → Lean mapping
* Section `client`: the context `rc:random_counter`, `L: counterG Σ` is
  `[rc : random_counter GF] (L : rc.counterG GF)`.
* `con_prog`, `con_prog_spec`: same names.
  - `con_prog` is a Rocq `expr` (`λ: "_", ...` not a value), transcribed with the `cpl`
    notation; `#4*"v" + "v'"` is `#4 * v + v'`.
  - In `con_prog_spec`, `P` has type `ℝ≥0∞ → (Fin 16 → ℝ≥0∞) → Fin 16 → IProp GF`; the
    hypothesis `⌜∀ x, 0 <= ε2 x⌝` is dropped (`ℝ≥0∞` errors are nonnegative);
    `SeriesC (λ n, 1 / 16 * ε2 n) <= ε` is `∑' n, 1 / 16 * ε2 n ≤ ε`;
    `RET #(fin_to_nat n)` is `RET LitV (LitInt ((n : ℕ) : ℤ))`; the side condition `E ## ↑N`
    is a hypothesis before the triple.
  - `fin_force` (from `clutch/prelude/fin.v`) is a local helper `fin_force N x : Fin (N + 1)`
    (`x` if `x ≤ N`, the last element otherwise).
  - The Rocq mask juggling (`fupd_mask_frame_r`, `union_empty_l_L`, `state_update_mono_fupd'`)
    is done with the helpers `fupd_mask_frame_union_l`, `fupd_mask_frame_union_r`.
  - The Rocq `SeriesC_finite_foldr ... lra` computation is `sum_fin4_fin4` (a reindexing
    by `finProdFinEquiv`).

## Omitted
* The unused section variable `!spawnG Σ` (Rocq `Context`; it is used by no lemma of the
  file).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Examples.RandomCounter.RandomCounter

namespace Coneris.Examples.RandomCounter.Client2

/-! ## Helpers -/

/-- Rocq: `fin_force` (from `clutch/prelude/fin.v`): `x` as an element of `fin (S N)` if
`x ≤ N`, and `N` otherwise. -/
def fin_force (N x : ℕ) : Fin (N + 1) :=
  if h : x ≤ N then ⟨x, Nat.lt_succ_of_le h⟩ else Fin.last N

theorem fin_force_val (N x : ℕ) (h : x ≤ N) : (fin_force N x : ℕ) = x := by
  simp [fin_force, h]

/-- Helper: reindexing a sum over `fin 16` by pairs of `fin 4`. -/
theorem sum_fin4_fin4 (f : Fin 16 → ℝ≥0∞) :
    ∑ x : Fin 4, ∑ y : Fin 4, f (fin_force 15 (4 * x + y)) = ∑ n : Fin 16, f n := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (finProdFinEquiv.trans (finCongr (by norm_num))) _ _ ?_
  rintro ⟨x, y⟩
  congr 1
  ext
  rw [fin_force_val _ _ (by omega)]
  simp [finProdFinEquiv]
  omega

/-- Helper (Rocq: `rewrite SeriesC_finite_foldr/=. ... lra.`). -/
theorem presample_sum_fin16 (ε : ℝ≥0∞) (ε2 : Fin 16 → ℝ≥0∞)
    (Hsum : ∑' n, 1 / 16 * ε2 n ≤ ε) :
    ∑' x : Fin 4, 1 / 4 *
      (∑' y : Fin 4, 1 / 4 * ε2 (fin_force 15 (4 * (x : ℕ) + (y : ℕ)))) ≤ ε := by
  refine le_trans (le_of_eq ?_) Hsum
  simp only [tsum_fintype, Finset.mul_sum, ← mul_assoc]
  have h : (1 / 4 : ℝ≥0∞) * (1 / 4) = 1 / 16 := by
    simp only [one_div]
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  simp only [h]
  exact sum_fin4_fin4 (fun n => 1 / 16 * ε2 n)

section masks

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Helper (Rocq: `fupd_mask_frame_r` + `union_empty_l_L`). -/
theorem fupd_mask_frame_union_l {E : CoPset} {N : Namespace} (h : E ## ↑N) (P : IProp GF) :
    (|={E, ∅}=> P) ⊢ |={E ∪ ↑N, ↑N}=> P := by
  have H := fupd_mask_frame_right (PROP := IProp GF) (P := P) (E1 := E) (E2 := ∅)
    (Ef := ↑N) h
  rwa [LawfulSet.union_empty_left] at H

/-- Helper (Rocq: `fupd_mask_frame_r` + `union_empty_l_L`). -/
theorem fupd_mask_frame_union_r {E : CoPset} {N : Namespace} (P : IProp GF) :
    (|={∅, E}=> P) ⊢ |={↑N, E ∪ ↑N}=> P := by
  have H := fupd_mask_frame_right (PROP := IProp GF) (P := P) (E1 := ∅) (E2 := E)
    (Ef := ↑N) LawfulSet.disjoint_empty_left
  rwa [LawfulSet.union_empty_left] at H

end masks

/-! ## The client -/

section client

variable {GF : BundledGFunctors} [conerisGS GF] [rc : random_counter GF] (L : rc.counterG GF)

/-- Rocq: `con_prog`. -/
def con_prog : expr := cpl(
  λ _,
    let c := v(&rc.new_counter) #() in
    let lbl := v(&rc.allocate_tape) #() in
    (v(&rc.incr_counter_tape) c lbl);
    let v := v(&rc.read_counter) c in
    v(&rc.incr_counter_tape) c lbl;
    let v' := v(&rc.read_counter) c - v in
    #4 * v + v')

include L in
/-- Rocq: `con_prog_spec`. -/
theorem con_prog_spec (P : ℝ≥0∞ → (Fin 16 → ℝ≥0∞) → Fin 16 → IProp GF) (E : CoPset)
    (N : Namespace) (Hnotin : E ## ↑N) :
    {{ |={E, ∅}=>
        ∃ (ε : ℝ≥0∞) (ε2 : Fin 16 → ℝ≥0∞),
          ↯ ε ∗ ⌜∑' n, 1 / 16 * ε2 n ≤ ε⌝ ∗
          (∀ n, ↯ (ε2 n) ={∅, E}=∗ P ε ε2 n) }}
      cpl(&(con_prog (rc := rc)) #()) @ (E ∪ ↑N)
    {{ (n : Fin 16), RET LitV (LitInt ((n : ℕ) : ℤ)); ∃ ε ε2, P ε ε2 n }} := by
  iintro %Φ Hvs HΦ
  unfold con_prog
  wp_pures
  wp_apply rc.new_counter_spec L (E ∪ ↑N) N $$ [] with %c ⟨%γ, #Hcounter, Hfrag⟩
  · itrivial
  wp_pures
  wp_apply rc.allocate_tape_spec L N (E ∪ ↑N) c γ LawfulSet.union_subset_right $$ Hcounter
    with %lbl Htape
  wp_pures
  ihave H : iprop(state_update (E ∪ ↑N) (E ∪ ↑N)
      iprop(∃ (ε : ℝ≥0∞) (ε2 : Fin 16 → ℝ≥0∞) (n1 n2 : Fin 4) (n : Fin 16),
        ⌜(n : ℕ) = 4 * (n1 : ℕ) + (n2 : ℕ)⌝ ∗
        rc.counter_tapes L lbl [(n1 : ℕ), (n2 : ℕ)] ∗ P ε ε2 n)) $$ [Hvs Htape]
  · ihave Hvs := fupd_mask_frame_union_l Hnotin _ $$ Hvs
    imod Hvs with ⟨%ε, %ε2, Herr, %Hsum, Hvs⟩
    imod rc.counter_tapes_presample L N ↑N γ c lbl [] ε
      (fun x => ∑' y : Fin 4, 1 / 4 * ε2 (fin_force 15 (4 * (x : ℕ) + (y : ℕ))))
      LawfulSet.subset_refl (presample_sum_fin16 ε ε2 Hsum) $$ Hcounter Htape Herr
      with ⟨%n, Herr, Htape⟩
    imod rc.counter_tapes_presample L N ↑N γ c lbl _ _
      (fun x => ε2 (fin_force 15 (4 * (n : ℕ) + (x : ℕ))))
      LawfulSet.subset_refl (le_refl _) $$ Hcounter Htape Herr
      with ⟨%n', Herr, Htape⟩
    ihave H := fupd_mask_frame_union_r (N := N) _ $$ [Hvs Herr]
    · iapply Hvs $$ Herr
    imod H
    imodintro
    iexists ε, ε2, n, n', fin_force 15 (4 * (n : ℕ) + (n' : ℕ))
    simp only [List.nil_append, List.cons_append]
    iframe
    ipureintro
    exact fin_force_val _ _ (by omega)
  imod H with ⟨%ε, %ε2, %n1, %n2, %n, %Heq, Htape, HP⟩
  wp_apply rc.incr_counter_tape_spec_some L N (E ∪ ↑N) c γ
    (fun _ => rc.counter_content_frag L γ 1 (n1 : ℕ)) lbl (n1 : ℕ) [(n2 : ℕ)]
    LawfulSet.union_subset_right $$ [Htape Hfrag] with %z ⟨Htape, Hfrag⟩
  · iframe Htape
    isplitr
    · iexact Hcounter
    iintro %z Hauth
    imod rc.counter_content_update L γ _ z 0 (n1 : ℕ) $$ Hauth Hfrag with ⟨Hauth, Hfrag⟩
    imodintro
    rw [zero_add]
    iframe
  wp_pures
  wp_apply rc.read_counter_spec L N (E ∪ ↑N) c γ
    (fun n => iprop(rc.counter_content_frag L γ 1 (n1 : ℕ) ∗ ⌜n = (n1 : ℕ)⌝))
    LawfulSet.union_subset_right $$ [Hfrag] with %v ⟨Hfrag, %Hv⟩
  · iframe Hcounter
    iintro %z Hauth
    ihave %Heq' := rc.counter_content_agree L γ z (n1 : ℕ) $$ Hauth Hfrag
    imodintro
    iframe
    ipureintro
    exact Heq'.symm
  subst Hv
  wp_pures
  wp_apply rc.incr_counter_tape_spec_some L N (E ∪ ↑N) c γ
    (fun _ => rc.counter_content_frag L γ 1 ((n1 : ℕ) + (n2 : ℕ))) lbl (n2 : ℕ) []
    LawfulSet.union_subset_right $$ [Htape Hfrag] with %z' ⟨Htape, Hfrag⟩
  · iframe Htape
    isplitr
    · iexact Hcounter
    iintro %z Hauth
    imod rc.counter_content_update L γ _ z (n1 : ℕ) (n2 : ℕ) $$ Hauth Hfrag
      with ⟨Hauth, Hfrag⟩
    imodintro
    iframe
  wp_pures
  wp_apply rc.read_counter_spec L N (E ∪ ↑N) c γ
    (fun n => iprop(rc.counter_content_frag L γ 1 ((n1 : ℕ) + (n2 : ℕ)) ∗
      ⌜n = (n1 : ℕ) + (n2 : ℕ)⌝))
    LawfulSet.union_subset_right $$ [Hfrag] with %v' ⟨Hfrag, %Hv'⟩
  · iframe Hcounter
    iintro %z Hauth
    ihave %Heq' := rc.counter_content_agree L γ z ((n1 : ℕ) + (n2 : ℕ)) $$ Hauth Hfrag
    imodintro
    iframe
    ipureintro
    exact Heq'.symm
  subst Hv'
  wp_pures
  have h : 4 * (((n1 : ℕ) : ℤ)) + (((n2 : ℕ) : ℤ)) = (((n : ℕ) : ℤ)) := by
    rw [Heq]
    push_cast
    ring
  rw [h]
  imodintro
  iapply HΦ
  iexists ε, ε2
  iexact HP

end client

end Coneris.Examples.RandomCounter.Client2
