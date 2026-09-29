module

public import Metrology.Coneris.Examples.BloomFilter.ConcurrentBloomFilterAltPart2
public import Metrology.Coneris.Examples.BloomFilter.ConcurrentBloomFilterAltPart3

/-!
# A concurrent Bloom filter, part 4: lookups and the main program

Ported from clutch/theories/coneris/examples/bloom_filter/concurrent_bloom_filter_alt.v
(`bloom_filter_lookup_spec`, `main_bloom_filter_seq_spec`). See
`Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt` for the name map.

## Rocq → Lean map
* Same names. The Rocq statement `(k ∉ ks) -> (k ≤ max_key) -> ([∗ list] ..) -∗ {{{ .. }}}`
  is kept as pure hypotheses followed by `⊢ ([∗list] ..) -∗ {{ .. }} .. {{ .. }}`;
  `{{{ v, RET v; ⌜v = #false⌝ }}}` is `{{ v, RET v; ⌜v = LitV (LitBool false)⌝ }}`.
* The `nonnegreal`s `mknonnegreal ((size s / (filter_size + 1)) ^ z) _` and `0%NNR` given to
  `wp_hash_lookup_avoid_set` are the `ℝ≥0∞` values `p ^ z` (with
  `p := (s.card : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1)`) and `0`.
* `ec_contradict` is `ErrorCredit.contradict`; `big_sepS_elem_of` (on the list encoding of
  `set_seq 0 (S max_key) ∖ list_to_set ks`, see part 1) is `BigSepL.bigSepL_mem`;
  `list_elem_of_lookup_2` is `List.mem_of_getElem?`.
* The Rocq file has no adequacy corollary (it stops at `main_bloom_filter_seq_spec`, and
  `main_bloom_filter` has no spec), so none is ported.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option linter.iris.dupNamespace false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.List Coneris.Lib.Array Coneris.Lib.Spawn Coneris.Lib.Par
open Coneris.Examples.HashDir.ConHashInterface4
open Coneris.Examples.BloomFilter.BloomFilter (fp_error fp_error_max fp_error_zero)

namespace Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt

section conc_bloom_filter

variable (filter_size max_key num_hash : ℕ)
variable {GF : BundledGFunctors} [conerisGS GF] [c : con_hash4 GF]

set_option linter.unusedVariables false in
/-- Rocq: `bloom_filter_lookup_spec`. (The hypotheses `Hk`, `Hkleq` are unused, as in Rocq.) -/
theorem bloom_filter_lookup_spec (N : Namespace) (bfl : Loc) (hfuns : val) (a : Loc)
    (hnames : List (GName × GName × GName)) (k : ℕ) (ks : List ℕ) (s : Finset ℕ)
    (Hk : k ∉ ks) (Hkleq : k ≤ max_key) :
    ⊢ ([∗list] k ∈ ks, ⌜k ≤ max_key⌝) -∗
      {{ ↯ (fp_error filter_size num_hash 0 s.card) ∗
          ([∗list] γ ∈ hnames, c.hashkey γ k none) ∗
          bloom_filter_inv filter_size num_hash N bfl hfuns a hnames ks s }}
        cpl(&lookup_bloom_filter #bfl #k)
      {{ v, RET v; ⌜v = LitV (LitBool false)⌝ }} := by
  iintro -
  iintro !> %Φ ⟨Herr, Hfrags, #Hinv⟩ HΦ
  unfold lookup_bloom_filter
  wp_pures
  wp_bind (Load _)
  unfold bloom_filter_inv
  iinv Hinv with ⟨%hfs, >Hbfl, >%Hhfs, >%Hlen, #Hhinv, >%Hbound, Harr⟩ Hclose
  wp_load
  imod Hclose $$ [Hbfl Harr]
  · inext
    iexists hfs
    iframe Hbfl
    isplitr
    · ipureintro; exact Hhfs
    isplitr
    · ipureintro; exact Hlen
    isplitr
    · iexact Hhinv
    isplitr
    · ipureintro; exact Hbound
    iexact Harr
  imodintro
  wp_pures
  wp_alloc res as Hres
  wp_pures
  -- `p` is Rocq's `size s / (filter_size + 1)`
  set p : ℝ≥0∞ := (s.card : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1) with Hp
  wp_apply wp_list_iter_invariant_HO
      (fun _ fs2 => iprop(
        (∃ hnames2,
          ([∗list] γ ∈ hnames2, c.hashkey γ k none) ∗
          con_hash_inv_list filter_size fs2 hnames2 ks s) ∗
        (res ↦ LitV (LitBool false) ∨
          (res ↦ LitV (LitBool true) ∗ ↯ (p ^ fs2.length))))) hfs _ hfuns
    $$ [] [Hfrags Herr Hres] with ⟨-, Hr⟩
  · iintro %fs1 %f %fs2 !> %Ψ ⟨⟨%γ2, Hfrags, Hiter⟩, Hr⟩ HΨ
    icases con_hash_inv_list_cons filter_size f fs2 γ2 ks s $$ Hiter
      with ⟨%γ, %hnames3, %Heq, #Hinvf, -, Htail⟩
    subst Heq
    icases Hfrags with ⟨Hknone, Hfrags⟩
    icases Hr with (Hr | ⟨Hr, Herr⟩)
    · -- `res ↦ #false`
      wp_pures
      wp_apply wp_hash_lookup_safe k f γ filter_size $$ [Hknone] with %v ⟨%Hv, #Hsome⟩
      · iframe Hknone Hinvf
      wp_pures
      wp_bind (Load _)
      iinv Hinv with ⟨%hfs', Hbfl, Hhfs', Hlen', Hhinv', Hbound', %arr, Harr, >%HlenA, >%Htf,
        >%Htrue⟩ Hclose
      obtain ⟨x, Hx⟩ : ∃ x, arr[v]? = some x :=
        ⟨arr[v]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      wp_apply wp_load_offset a (DFrac.own 1) v arr x Hx $$ Harr with Harr
      imod Hclose $$ [Hbfl Hhfs' Hlen' Hhinv' Hbound' Harr]
      · inext
        iexists hfs'
        iframe Hbfl Hhfs' Hlen' Hhinv' Hbound'
        iexists arr
        iframe Harr
        ipureintro
        exact ⟨HlenA, Htf, Htrue⟩
      imodintro
      rcases Htf v (by omega) with Hx' | Hx' <;> rw [Hx] at Hx' <;> cases Hx'
      · wp_pures
        iapply HΨ
        iframe Hr
        iexists hnames3
        iframe Hfrags Htail
      · wp_pures
        wp_apply wp_store $$ Hr with Hr
        iapply HΨ
        iframe Hr
        iexists hnames3
        iframe Hfrags Htail
    · -- `res ↦ #true`
      wp_pures
      simp only [List.length_cons]
      wp_apply wp_hash_lookup_avoid_set k f γ s (p ^ (fs2.length + 1)) (p ^ fs2.length) 0
          filter_size Hbound (by
            rw [zero_mul, add_zero, pow_succ, mul_assoc, Hp,
              ENNReal.div_mul_cancel (by simp) (by simp), mul_comm]) $$ [Herr Hknone]
        with %v ⟨%Hv, Hcases, #Hsome⟩
      · iframe Herr Hknone Hinvf
      icases Hcases with (⟨%Hin, Herr⟩ | ⟨%Hout, Herr⟩)
      · -- `v ∈ s`
        wp_pures
        wp_bind (Load _)
        iinv Hinv with ⟨%hfs', Hbfl, Hhfs', Hlen', Hhinv', Hbound', %arr, Harr, >%HlenA, >%Htf,
          >%Htrue⟩ Hclose
        obtain ⟨x, Hx⟩ : ∃ x, arr[v]? = some x :=
          ⟨arr[v]'(by omega), List.getElem?_eq_getElem (by omega)⟩
        wp_apply wp_load_offset a (DFrac.own 1) v arr x Hx $$ Harr with Harr
        imod Hclose $$ [Hbfl Hhfs' Hlen' Hhinv' Hbound' Harr]
        · inext
          iexists hfs'
          iframe Hbfl Hhfs' Hlen' Hhinv' Hbound'
          iexists arr
          iframe Harr
          ipureintro
          exact ⟨HlenA, Htf, Htrue⟩
        imodintro
        rcases Htf v (by omega) with Hx' | Hx' <;> rw [Hx] at Hx' <;> cases Hx'
        · wp_pures
          iapply HΨ
          isplitl [Hfrags Htail]
          · iexists hnames3
            iframe Hfrags Htail
          iright
          iframe Hr Herr
        · wp_pures
          wp_apply wp_store $$ Hr with Hr
          iapply HΨ
          iframe Hr
          iexists hnames3
          iframe Hfrags Htail
      · -- `v ∉ s`: the bit `v` of the array is `false`
        wp_pures
        wp_bind (Load _)
        iinv Hinv with ⟨%hfs', Hbfl, Hhfs', Hlen', Hhinv', Hbound', %arr, Harr, >%HlenA, >%Htf,
          >%Htrue⟩ Hclose
        have Hlookup : arr[v]? = some (LitV (LitBool false)) := by
          rcases Htf v (by omega) with H1 | H2
          · exact absurd (Htrue v (by omega) H1) Hout
          · exact H2
        wp_apply wp_load_offset a (DFrac.own 1) v arr _ Hlookup $$ Harr with Harr
        imod Hclose $$ [Hbfl Hhfs' Hlen' Hhinv' Hbound' Harr]
        · inext
          iexists hfs'
          iframe Hbfl Hhfs' Hlen' Hhinv' Hbound'
          iexists arr
          iframe Harr
          ipureintro
          exact ⟨HlenA, Htf, Htrue⟩
        imodintro
        wp_pures
        wp_apply wp_store $$ Hr with Hr
        iapply HΨ
        iframe Hr
        iexists hnames3
        iframe Hfrags Htail
  · isplitr
    · ipureintro; exact Hhfs
    isplitl [Hfrags]
    · iexists hnames
      iframe Hfrags
      iexact Hhinv
    iright
    iframe Hres
    rw [Hlen]
    by_cases H : s.card ≥ filter_size + 1
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

/-- Rocq: `main_bloom_filter_seq_spec`. -/
theorem main_bloom_filter_seq_spec (N : Namespace) (ks : List ℕ) (ksv : val) (ktest : ℕ)
    (Hndup : ks.Nodup) (Hksv : is_list ks ksv) (Hktest : ktest ∉ ks)
    (Htestvalid : ktest ≤ max_key) :
    {{ ([∗list] k ∈ ks, ⌜k ≤ max_key⌝) ∗
        (↯ (fp_error filter_size num_hash (num_hash * ks.length) 0) : IProp GF) }}
      (main_bloom_filter_seq filter_size max_key num_hash (c := c) ksv (LitV (LitInt ktest)))
    {{ v, RET v; ⌜v = LitV (LitBool false)⌝ }} := by
  iintro %Φ ⟨#Hks, Herr⟩ HΦ
  unfold main_bloom_filter_seq
  wp_apply bloom_filter_init_spec filter_size max_key num_hash N ks Hndup $$ Hks Herr
    with %bfl ⟨%hfuns, %a, %hnames, %s, Herr, Hauths, #Hinv⟩
  wp_pures
  wp_apply insert_bloom_filter_loop_seq_spec filter_size max_key num_hash N bfl hfuns a hnames
      s ks ks ksv Hksv $$ [] with %v -
  · isplitr
    · iexact Hinv
    isplitr
    · iapply (BigSepL.bigSepL_pure (φ := fun (_ : ℕ) (k : ℕ) => k ∈ ks) (l := ks)).2
      ipureintro
      intro i x Hx
      exact List.mem_of_getElem? Hx
    iexact Hks
  wp_pures
  wp_apply bloom_filter_lookup_spec filter_size max_key num_hash N bfl hfuns a hnames ktest ks s
      Hktest Htestvalid $$ Hks [Herr Hauths] with %v %Hv
  · iframe Herr Hinv
    iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Hauths
    intro _ γ
    have Hmem : ktest ∈ (List.range (max_key + 1)).filter (· ∉ ks) := by
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, Hktest⟩
    exact BigSepL.bigSepL_mem (Φ := fun k => c.hashkey γ k none) Hmem
  iapply HΦ
  ipureintro
  exact Hv

end conc_bloom_filter

end Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt
