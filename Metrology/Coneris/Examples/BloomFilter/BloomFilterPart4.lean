module

public import Metrology.Coneris.Examples.BloomFilter.BloomFilter

/-!
# A (sequential) Bloom filter, part 4: lookups

Ported from clutch/theories/coneris/examples/bloom_filter/bloom_filter.v
(`bloom_filter_lookup_in_spec`, `bloom_filter_lookup_not_in_spec`). See
`Coneris.Examples.BloomFilter.BloomFilter` for the name map.

## Rocq → Lean map
* `bloom_filter_lookup_in_spec`, `bloom_filter_lookup_not_in_spec`: same names;
  `{{{ v, RET v; ⌜v = #true⌝ }}}` is `{{ v, RET v; ⌜v = LitV (LitBool true)⌝ }}`.
* `ec_weaken` is `ErrorCredit.weaken`, `ec_contradict` is `ErrorCredit.contradict`.
* In `bloom_filter_lookup_not_in_spec`, the `nonnegreal`s
  `mknonnegreal ((size idxs / (filter_size + 1)) ^ z) _` and `0%NNR` are the `ℝ≥0∞` values
  `((idxs.card : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1)) ^ z` and `0`.
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

/-- Rocq: `bloom_filter_lookup_in_spec`. -/
theorem bloom_filter_lookup_in_spec (l : Loc) (s : Finset ℕ) (x rem : ℕ) :
    {{ is_bloom_filter filter_size num_hash l s rem ∗ ⌜x ∈ s⌝ }}
      cpl(&lookup_bloom_filter #l #x)
    {{ v, RET v; (⌜v = LitV (LitBool true)⌝ : IProp GF) }} := by
  iintro %Φ ⟨Hbf, %Hx⟩ HΦ
  unfold lookup_bloom_filter
  wp_pures
  unfold is_bloom_filter
  icases Hbf with ⟨%hfuns, %hs, %ms, %a, %arr, %idxs, Herr, Hl, %Hhfuns, %Hlenhs, Hhs, %HlenA,
    %HsizeIdxs, Ha, %Hms, %Hidxs, %Htrue, %Hbd, %Hfalse⟩
  wp_load
  wp_pures
  wp_alloc res as Hres
  wp_pures
  wp_apply wp_list_iter_invariant_HO
      (fun l1 l2 => iprop(
        (∃ ms_old : List hmap,
          ⌜∀ m ∈ ms_old, s = hmap_dom m⌝ ∗
          ⌜∀ e : ℕ, e ∈ s → ∀ m ∈ ms_old, m.getD e 0 ∈ idxs⌝ ∗
          [∗list] h;m ∈ l2;ms_old, hashfun filter_size h m) ∗
        a ↦∗ arr ∗
        ⌜is_list_HO (l1 ++ l2) hfuns⌝ ∗
        res ↦ LitV (LitBool true))) hs _ hfuns
    $$ [] [Ha Hhs Hres] with ⟨-, Ha, -, Hr⟩
  · iintro %lpre %w %lsuf !> %Ψ ⟨⟨%ms_old, %Hms_old_dom, %Hms_old_idxs, Hms_old_hf⟩, Ha,
      %Hhfuns', Hr⟩ HΨ
    wp_pures
    cases ms_old with
    | nil =>
      ihave %Hlen := BigSepL2.bigSepL2_length $$ Hms_old_hf
      simp at Hlen
    | cons m ms_tail =>
    icases Hms_old_hf with ⟨Hmcur, Hms_tail⟩
    have Hmem : x ∈ m := by
      rw [← mem_hmap_dom, ← Hms_old_dom m List.mem_cons_self]
      exact Hx
    obtain ⟨x0, H⟩ : ∃ x0, m[x]? = some x0 :=
      Option.isSome_iff_exists.mp (Std.ExtTreeMap.isSome_getElem?_iff_mem.mpr Hmem)
    wp_apply wp_hashfun_prev filter_size ⊤ w m x x0 H $$ Hmcur with Hhfw
    wp_pures
    have Hx0 : x0 ∈ idxs := by
      have := Hms_old_idxs x Hx m List.mem_cons_self
      rwa [Std.ExtTreeMap.getD_eq_getD_getElem?, H, Option.getD_some] at this
    wp_apply wp_load_offset a (DFrac.own 1) x0 arr _ (Htrue x0 Hx0) $$ Ha with Ha
    wp_pures
    iapply HΨ
    isplitl [Hms_tail]
    · iexists ms_tail
      iframe
      ipureintro
      exact ⟨fun m' Hm' => Hms_old_dom m' (List.mem_cons_of_mem _ Hm'),
        fun e He m' Hm' => Hms_old_idxs e He m' (List.mem_cons_of_mem _ Hm')⟩
    iframe
    ipureintro
    simpa using Hhfuns'
  · isplitr
    · ipureintro; exact Hhfuns
    isplitl [Hhs]
    · iexists ms
      iframe
      ipureintro
      exact ⟨Hms, Hidxs⟩
    iframe
    ipureintro
    simpa using Hhfuns
  wp_pures
  wp_load
  iapply HΦ
  ipureintro
  rfl

/-- Rocq: `bloom_filter_lookup_not_in_spec`. -/
theorem bloom_filter_lookup_not_in_spec (l : Loc) (s : Finset ℕ) (x rem : ℕ) :
    {{ is_bloom_filter filter_size num_hash l s (rem + 1) ∗ ⌜x ∉ s⌝ }}
      cpl(&lookup_bloom_filter #l #x)
    {{ v, RET v; (⌜v = LitV (LitBool false)⌝ : IProp GF) }} := by
  iintro %Φ ⟨Hbf, %Hx⟩ HΦ
  unfold lookup_bloom_filter
  wp_pures
  unfold is_bloom_filter
  icases Hbf with ⟨%hfuns, %hs, %ms, %a, %arr, %idxs, Herr, Hl, %Hhfuns, %Hlenhs, Hhs, %HlenA,
    %HsizeIdxs, Ha, %Hms, %Hidxs, %Htrue, %Hbd, %Hfalse⟩
  wp_load
  wp_pures
  wp_alloc res as Hres
  wp_pures
  ihave Herr := ErrorCredit.weaken
    (fp_error_weaken filter_size num_hash (num_hash * (rem + 1)) idxs.card) $$ Herr
  -- `p` is Rocq's `size idxs / (filter_size + 1)`
  set p : ℝ≥0∞ := (idxs.card : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1) with Hp
  wp_apply wp_list_iter_invariant_HO
      (fun l1 l2 => iprop(
        (∃ ms_old : List hmap,
          ⌜∀ m ∈ ms_old, s = hmap_dom m⌝ ∗
          [∗list] h;m ∈ l2;ms_old, hashfun filter_size h m) ∗
        a ↦∗ arr ∗
        ⌜is_list_HO (l1 ++ l2) hfuns⌝ ∗
        (res ↦ LitV (LitBool false) ∨
          (res ↦ LitV (LitBool true) ∗ ↯ (p ^ l2.length))))) hs _ hfuns
    $$ [] [Ha Hhs Herr Hres] with ⟨-, Ha, -, Hr⟩
  · iintro %lpre %w %lsuf !> %Ψ ⟨⟨%ms_old, %Hms_old_dom, Hms_old_hf⟩, Ha, %Hhfuns', Hr⟩ HΨ
    wp_pures
    cases ms_old with
    | nil =>
      ihave %Hlen := BigSepL2.bigSepL2_length $$ Hms_old_hf
      simp at Hlen
    | cons m ms_tail =>
    icases Hms_old_hf with ⟨Hmcur, Hms_tail⟩
    have Hnone : m[x]? = none := by
      rw [Std.ExtTreeMap.getElem?_eq_none]
      rw [← mem_hmap_dom, ← Hms_old_dom m List.mem_cons_self]
      exact Hx
    have Hms_tail_dom : ∀ m' ∈ ms_tail, s = hmap_dom m' :=
      fun m' Hm' => Hms_old_dom m' (List.mem_cons_of_mem _ Hm')
    icases Hr with (Hr | ⟨Hr, Herr⟩)
    · wp_apply wp_insert_basic filter_size ⊤ w m x Hnone $$ Hmcur with %v ⟨%Hv, Hhfw⟩
      wp_pures
      by_cases Hvi : v ∈ idxs
      · wp_apply wp_load_offset a (DFrac.own 1) v arr _ (Htrue v Hvi) $$ Ha with Ha
        wp_pures
        iapply HΨ
        isplitl [Hms_tail]
        · iexists ms_tail
          iframe
          ipureintro
          exact Hms_tail_dom
        iframe
        ipureintro
        simpa using Hhfuns'
      · wp_apply wp_load_offset a (DFrac.own 1) v arr _ (Hfalse v Hv Hvi) $$ Ha with Ha
        wp_pures
        wp_apply wp_store $$ Hr with Hr
        iapply HΨ
        isplitl [Hms_tail]
        · iexists ms_tail
          iframe
          ipureintro
          exact Hms_tail_dom
        iframe
        ipureintro
        simpa using Hhfuns'
    · simp only [List.length_cons]
      wp_apply wp_insert_avoid_set_adv filter_size ⊤ w m x idxs (p ^ (lsuf.length + 1))
          (p ^ lsuf.length) 0 Hnone Hbd (by rw [zero_mul, ENNReal.zero_div, add_zero,
            mul_div_assoc, ← Hp, pow_succ]) $$ [Herr Hmcur] with %v ⟨%Hv, Hhfw, Herr⟩
      · iframe
      icases Herr with (⟨%Hvout, Herr⟩ | ⟨%Hvin, Herr⟩)
      · wp_pures
        wp_apply wp_load_offset a (DFrac.own 1) v arr _ (Hfalse v Hv Hvout) $$ Ha with Ha
        wp_pures
        wp_apply wp_store $$ Hr with Hr
        iapply HΨ
        isplitl [Hms_tail]
        · iexists ms_tail
          iframe
          ipureintro
          exact Hms_tail_dom
        iframe
        ipureintro
        simpa using Hhfuns'
      · wp_pures
        wp_apply wp_load_offset a (DFrac.own 1) v arr _ (Htrue v Hvin) $$ Ha with Ha
        wp_pures
        iapply HΨ
        isplitl [Hms_tail]
        · iexists ms_tail
          iframe
          ipureintro
          exact Hms_tail_dom
        isplitl [Ha]
        · iexact Ha
        isplitr
        · ipureintro
          simpa using Hhfuns'
        iright
        iframe
  · isplitr
    · ipureintro; exact Hhfuns
    isplitl [Hhs]
    · iexists ms
      iframe
      ipureintro
      exact Hms
    iframe
    isplitr
    · ipureintro
      simpa using Hhfuns
    iright
    iframe
    rw [Hlenhs]
    by_cases H : idxs.card ≥ filter_size + 1
    · rw [fp_error_max _ _ 0 _ H]
      iexfalso
      iapply ErrorCredit.contradict le_rfl $$ Herr
    · rw [fp_error_zero _ _ _ H]
      iexact Herr
  icases Hr with (Hr | ⟨Hr, Herr⟩)
  · wp_pures
    wp_load
    iapply HΦ
    ipureintro
    rfl
  · simp only [List.length_nil, pow_zero]
    iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Herr

end bloom_filter

end Coneris.Examples.BloomFilter.BloomFilter
