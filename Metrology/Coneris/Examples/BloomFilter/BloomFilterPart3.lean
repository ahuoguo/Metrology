module

public import Metrology.Coneris.Examples.BloomFilter.BloomFilter

/-!
# A (sequential) Bloom filter, part 3: insertion

Ported from clutch/theories/coneris/examples/bloom_filter/bloom_filter.v
(`bloom_filter_insert_spec`). See `Coneris.Examples.BloomFilter.BloomFilter` for the name map.

## Rocq → Lean map
* `bloom_filter_insert_spec`: same name; `S rem` is `rem + 1`; `RET #()` is `RET LitV LitUnit`.
* The `nonnegreal`s `mknonnegreal (fp_error ..) _` passed to `wp_insert_avoid_set_adv` are the
  `ℝ≥0∞` values `fp_error ..`.
* Rocq's `iAssert (is_bloom_filter_partial l x s rem [] hs a)` is proved directly as the
  precondition of `wp_list_iter_invariant_HO`.

## Added
* `fp_error_step`: the error equation required by `wp_insert_avoid_set_adv` (Rocq proves it
  inline with `case_bool_decide`, `fp_error_max` and real rewriting).
* `insert_step_pure`: the pure goals of the invariant step (Rocq: the two `repeat split` blocks,
  proved inline). Both cases of `wp_insert_avoid_set_adv` are handled with the new index set
  `{v} ∪ idxs`: in the case `v ∈ idxs` Rocq keeps `idxs`, which is equal to `{v} ∪ idxs`
  (the error credit is rewritten along this equality). The bound
  `size ({v} ∪ idxs) ≤ filter_size + 1` is proved from `{v} ∪ idxs ⊆ range (filter_size + 1)`
  (Rocq: via `idxs ⊆ set_seq 0 (filter_size + 1) ∖ {[v]}` in the case `v ∉ idxs`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option linter.iris.dupNamespace false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.List Coneris.Lib.Array Coneris.Examples.Hash

namespace Coneris.Examples.BloomFilter.BloomFilter

section bloom_filter

variable (filter_size num_hash : ℕ)
variable {GF : BundledGFunctors} [conerisGS GF] [HinG : SetBijG GF ℕ ℕ pairset]

/-- The error arithmetic of one hash insertion (Rocq: inline in `bloom_filter_insert_spec`,
by `case_bool_decide`, `fp_error_max` and real arithmetic): the form required by
`wp_insert_avoid_set_adv`. -/
theorem fp_error_step (K b : ℕ) (Hb : b ≤ filter_size + 1) :
    fp_error filter_size num_hash (K + 1) b =
      fp_error filter_size num_hash K b * b / ((filter_size : ℝ≥0∞) + 1) +
        fp_error filter_size num_hash K (b + 1) * ((filter_size : ℝ≥0∞) + 1 - b) /
          ((filter_size : ℝ≥0∞) + 1) := by
  by_cases H : b ≥ filter_size + 1
  · rw [fp_error_max _ _ (K + 1) b H, fp_error_max _ _ K b H,
      fp_error_max _ _ K (b + 1) (by omega), one_mul, one_mul,
      div_add_div_one_aux _ _ Hb]
  · rw [fp_error_succ _ _ _ _ H, mul_div_assoc, mul_div_assoc, mul_comm _ (_ / _),
      mul_comm (fp_error _ _ _ (b + 1))]

/-- The pure part of the invariant step of `bloom_filter_insert_spec` (Rocq: the
`repeat split` goals, proved inline). In both cases of `wp_insert_avoid_set_adv` the new set of
indices is `{v} ∪ idxs` (in the case `v ∈ idxs`, Rocq keeps `idxs`, which is the same set). -/
theorem insert_step_pure (x : ℕ) (s : Finset ℕ)
    (ms_new ms_old_tl : List hmap) (mcur : hmap) (arr : List val) (idxs : Finset ℕ) (v : ℕ)
    (Hv : v < filter_size + 1)
    (HlenA : arr.length = filter_size + 1)
    (Hms_old_cur : s = hmap_dom mcur) (Hms_old_tl : ∀ m ∈ ms_old_tl, s = hmap_dom m)
    (Hms_new : ∀ m ∈ ms_new, ({x} ∪ s) = hmap_dom m)
    (Hidxs_old : ∀ e, e ∈ s → ∀ m ∈ mcur :: ms_old_tl, m.getD e 0 ∈ idxs)
    (Hidxs_new : ∀ e, e ∈ ({x} ∪ s) → ∀ m ∈ ms_new, m.getD e 0 ∈ idxs)
    (Htrue : ∀ i, i ∈ idxs → arr[i]? = some (LitV (LitBool true)))
    (Hbd : ∀ i, i ∈ idxs → i < filter_size + 1)
    (Hfalse : ∀ i, i < filter_size + 1 → i ∉ idxs → arr[i]? = some (LitV (LitBool false))) :
    (arr.set v (LitV (LitBool true))).length = filter_size + 1 ∧
    ({v} ∪ idxs).card ≤ filter_size + 1 ∧
    (∀ m ∈ ms_old_tl, s = hmap_dom m) ∧
    (∀ m ∈ ms_new ++ [mcur.insert x v], ({x} ∪ s) = hmap_dom m) ∧
    (∀ e, e ∈ s → ∀ m ∈ ms_old_tl, m.getD e 0 ∈ ({v} ∪ idxs)) ∧
    (∀ e, e ∈ ({x} ∪ s) → ∀ m ∈ ms_new ++ [mcur.insert x v], m.getD e 0 ∈ ({v} ∪ idxs)) ∧
    (∀ i, i ∈ ({v} ∪ idxs) → (arr.set v (LitV (LitBool true)))[i]? = some (LitV (LitBool true))) ∧
    (∀ i, i ∈ ({v} ∪ idxs) → i < filter_size + 1) ∧
    (∀ i, i < filter_size + 1 → i ∉ ({v} ∪ idxs) →
      (arr.set v (LitV (LitBool true)))[i]? = some (LitV (LitBool false))) := by
  refine ⟨by rw [List.length_set, HlenA], ?_, Hms_old_tl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Rocq: `{[v]} ∪ idxs ⊆ set_seq 0 (filter_size + 1)`
    have Hsub : ({v} ∪ idxs) ⊆ Finset.range (filter_size + 1) := by
      intro i Hi
      rw [Finset.mem_union, Finset.mem_singleton] at Hi
      rw [Finset.mem_range]
      rcases Hi with rfl | Hi
      · exact Hv
      · exact Hbd i Hi
    simpa using Finset.card_le_card Hsub
  · intro m Hm
    rw [List.mem_append, List.mem_singleton] at Hm
    rcases Hm with Hm | rfl
    · exact Hms_new m Hm
    · rw [hmap_dom_insert, Hms_old_cur]
  · intro e He m Hm
    exact Finset.mem_union_right _ (Hidxs_old e He m (List.mem_cons_of_mem _ Hm))
  · intro e He m Hm
    rw [List.mem_append, List.mem_singleton] at Hm
    rcases Hm with Hm | rfl
    · exact Finset.mem_union_right _ (Hidxs_new e He m Hm)
    · by_cases Hex : e = x
      · subst Hex
        rw [Std.ExtTreeMap.getD_insert_self]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
      · rw [Std.ExtTreeMap.getD_insert, ite_eq_right_of_eq_false _ _ (eq_false (by
          rw [Nat.compare_eq_eq]; exact fun h => Hex h.symm))]
        rw [Finset.mem_union, Finset.mem_singleton] at He
        rcases He with rfl | He
        · exact absurd rfl Hex
        · exact Finset.mem_union_right _ (Hidxs_old e He mcur List.mem_cons_self)
  · intro i Hi
    rw [List.getElem?_set]
    by_cases Hvi : v = i
    · subst Hvi; simp [HlenA, Hv]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false Hvi)]
      rw [Finset.mem_union, Finset.mem_singleton] at Hi
      rcases Hi with rfl | Hi
      · exact absurd rfl Hvi
      · exact Htrue i Hi
  · intro i Hi
    rw [Finset.mem_union, Finset.mem_singleton] at Hi
    rcases Hi with rfl | Hi
    · exact Hv
    · exact Hbd i Hi
  · intro i Hleq Hi
    rw [Finset.mem_union, Finset.mem_singleton, not_or] at Hi
    rw [List.getElem?_set, ite_eq_right_of_eq_false _ _ (eq_false (fun h => Hi.1 h.symm))]
    exact Hfalse i Hleq Hi.2

/-- Rocq: `bloom_filter_insert_spec`. -/
theorem bloom_filter_insert_spec (l : Loc) (s : Finset ℕ) (x rem : ℕ) :
    {{ is_bloom_filter filter_size num_hash l s (rem + 1) ∗ ⌜x ∉ s⌝ }}
      cpl(&insert_bloom_filter #l #x)
    {{ RET LitV LitUnit; (is_bloom_filter filter_size num_hash l (s ∪ {x}) rem : IProp GF) }} := by
  iintro %Φ ⟨Hbf, %Hx⟩ HΦ
  unfold insert_bloom_filter
  wp_pures
  unfold is_bloom_filter
  icases Hbf with ⟨%hfuns, %hs, %ms, %a, %arr, %idxs, Herr, Hl, %Hfuns, %Hlenhs, Hhs, %HlenA,
    %HsizeIdxs, Ha, %Hms, %Hidxs, %Htrue, %Hbd, %Hfalse⟩
  rw [show num_hash * (rem + 1) = num_hash * rem + num_hash by ring]
  wp_load
  wp_pures
  wp_apply wp_list_iter_invariant_HO
      (fun l1 l2 => is_bloom_filter_partial filter_size num_hash l x s rem l1 l2 a) hs _ hfuns
    $$ [] [Herr Hl Hhs Ha] with Hbf
  · iintro %lpre %w %lsuf !> %Ψ Hbfp HK
    wp_pures
    unfold is_bloom_filter_partial
    icases Hbfp with ⟨%hfuns', %ms_new, %ms_old, %arr', %idxs', Herr, Hl, %Hhfuns, %Hlenhs',
      Hhs_new, Hhs_old, %HlenA', %HsizeIdxs', Ha, %Hms_old, %Hms_new, %Hidxs_old, %Hidxs_new,
      %Htrue', %Hbd', %Hfalse'⟩
    cases ms_old with
    | nil =>
      ihave %Hlen := BigSepL2.bigSepL2_length $$ Hhs_old
      simp at Hlen
    | cons mcur ms_old_tl =>
    icases Hhs_old with ⟨Hhs_cur, Hhs_rest⟩
    have Hcur : s = hmap_dom mcur := Hms_old mcur List.mem_cons_self
    have Hlookup : mcur[x]? = none := by
      rw [Std.ExtTreeMap.getElem?_eq_none]
      rw [← mem_hmap_dom, ← Hcur]
      exact Hx
    simp only [List.length_cons]
    rw [show num_hash * rem + (lsuf.length + 1) = (num_hash * rem + lsuf.length) + 1 by ring,
      fp_error_step _ _ _ _ HsizeIdxs']
    wp_apply wp_insert_avoid_set_adv filter_size ⊤ w mcur x idxs' _
        (fp_error filter_size num_hash (num_hash * rem + lsuf.length) idxs'.card)
        (fp_error filter_size num_hash (num_hash * rem + lsuf.length) (idxs'.card + 1))
        Hlookup Hbd' rfl $$ [Hhs_cur Herr] with %v ⟨%Hv, Hhfw, Hcases⟩
    · iframe
    have Hpure := insert_step_pure filter_size x s ms_new ms_old_tl
      mcur arr' idxs' v Hv HlenA' Hcur (fun m Hm => Hms_old m (List.mem_cons_of_mem _ Hm))
      Hms_new Hidxs_old Hidxs_new Htrue' Hbd' Hfalse'
    wp_pures
    wp_apply wp_store_offset a v arr' (LitV (LitBool true))
      ⟨arr'[v]'(by omega), List.getElem?_eq_getElem (by omega)⟩ $$ Ha with Ha
    iapply HK
    iexists hfuns', ms_new ++ [mcur.insert x v], ms_old_tl, arr'.set v (LitV (LitBool true)),
      {v} ∪ idxs'
    isplitl [Hcases]
    · icases Hcases with (⟨%Hvout, Herr⟩ | ⟨%Hvin, Herr⟩)
      · rw [Finset.card_union_of_disjoint (by simpa using Hvout), Finset.card_singleton,
          Nat.add_comm 1]
        iexact Herr
      · rw [show {v} ∪ idxs' = idxs' by simpa using Hvin]
        iexact Herr
    iframe Hl Ha
    isplitr
    · ipureintro; simpa using Hhfuns
    isplitr
    · ipureintro; simpa using Hlenhs'
    isplitl [Hhs_new Hhfw]
    · iapply BigSepL2.bigSepL2_snoc.2
      iframe
    isplitl [Hhs_rest]
    · iexact Hhs_rest
    obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9⟩ := Hpure
    ipureintro
    exact ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9⟩
  · isplitr
    · ipureintro; exact Hfuns
    unfold is_bloom_filter_partial
    iexists hfuns, [], ms, arr, idxs
    rw [Hlenhs]
    simp only [List.nil_append]
    iframe
    isplitr
    · ipureintro; exact Hfuns
    isplitr
    · ipureintro; exact Hlenhs
    isplitr
    · iempintro
    ipureintro
    exact ⟨HlenA, HsizeIdxs, Hms, by simp, Hidxs, by simp, Htrue, Hbd, Hfalse⟩
  ihave H := bloom_filter_from_partial filter_size num_hash l x s hs a rem $$ Hbf
  rw [Finset.union_comm]
  unfold is_bloom_filter
  iapply HΦ
  iexact H

end bloom_filter

end Coneris.Examples.BloomFilter.BloomFilter
