module

public import Metrology.Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt

/-!
# A concurrent Bloom filter, part 2: initialization

Ported from clutch/theories/coneris/examples/bloom_filter/concurrent_bloom_filter_alt.v
(`bloom_filter_init_spec`). See `Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt` for
the name map.

## Rocq → Lean map
* `bloom_filter_init_spec`: same name. The Rocq statement
  `NoDup ks -> ([∗ list] k ∈ ks, ⌜k ≤ max_key⌝) -∗ {{{ .. }}} .. {{{ .. }}}` is kept: a pure
  hypothesis, then `⊢ ([∗list] k ∈ ks, ⌜k ≤ max_key⌝) -∗ {{ .. }} .. {{ .. }}`.
  `RET #bfl` is `RET LitV (LitLoc bfl)`.
* The splitting of `[∗ set] k ∈ set_seq 0 (S max_key), hashkey γ k None` into the part on
  `list_to_set ks` and the part on `set_seq 0 (S max_key) ∖ list_to_set ks` (Rocq:
  `big_sepS_subseteq`, `union_difference`, `big_sepS_union`, `big_sepS_list_to_set`) is the
  helper `keys_split` on lists (see the map of part 1 for the list encoding of these sets).
* `iMod (inv_alloc ..)` is iris-lean's `inv_alloc`; `array.big_sepL_exists` is
  `Coneris.Lib.Array.big_sepL_exists`; `big_sepL2_sep_sepL_r` is
  `BigSepL2.bigSepL2_sep_sepL_right`.

## Added
* `keys_split` (see above).
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
open Coneris.Examples.BloomFilter.BloomFilter (fp_error fp_error_max fp_error_zero
  fp_error_succ fp_error_bounded fp_error_step div_le_one_aux div_add_div_one_aux)

namespace Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt

section conc_bloom_filter

variable (filter_size max_key num_hash : ℕ)
variable {GF : BundledGFunctors} [conerisGS GF] [c : con_hash4 GF]

/-- Splitting the keys `0 .. max_key` into `ks` and the other keys (Rocq: inline in
`bloom_filter_init_spec`, with `big_sepS_subseteq`, `union_difference`, `big_sepS_union` and
`big_sepS_list_to_set`). -/
theorem keys_split (ks : List ℕ) (Hndup : ks.Nodup) (Hks : ∀ k ∈ ks, k ≤ max_key)
    (P : ℕ → IProp GF) :
    ([∗list] k ∈ List.range (max_key + 1), P k) ⊢
      ([∗list] k ∈ ks, P k) ∗ [∗list] k ∈ (List.range (max_key + 1)).filter (· ∉ ks), P k := by
  have Hperm1 : ((List.range (max_key + 1)).filter (fun k => decide (k ∈ ks))).Perm ks := by
    rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) Hndup]
    intro k
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le (Hks k h), h⟩⟩
  have Hperm2 := List.filter_append_perm (fun k => decide (k ∈ ks)) (List.range (max_key + 1))
  have Hfilt : (List.range (max_key + 1)).filter (fun k => !decide (k ∈ ks)) =
      (List.range (max_key + 1)).filter (· ∉ ks) := by
    apply List.filter_congr
    intro k _
    simp
  rw [Hfilt] at Hperm2
  refine (BigSepL.bigSepL_perm Hperm2.symm).1.trans ?_
  refine BigSepL.bigSepL_append.1.trans ?_
  exact sep_mono_left (BigSepL.bigSepL_perm Hperm1).1

/-- Rocq: `bloom_filter_init_spec`. -/
theorem bloom_filter_init_spec (N : Namespace) (ks : List ℕ) (Hndup : ks.Nodup) :
    ⊢ ([∗list] k ∈ ks, ⌜k ≤ max_key⌝) -∗
      {{ ↯ (fp_error filter_size num_hash (num_hash * ks.length) 0) }}
        cpl(&(init_bloom_filter filter_size max_key num_hash (c := c)) #())
      {{ (bfl : Loc), RET LitV (LitLoc bfl);
          ∃ (hfuns : val) (a : Loc) (hnames : List (GName × GName × GName)) (s : Finset ℕ),
            ↯ (fp_error filter_size num_hash 0 s.card) ∗
            ([∗list] γ ∈ hnames,
              [∗list] k ∈ (List.range (max_key + 1)).filter (· ∉ ks), c.hashkey γ k none) ∗
            bloom_filter_inv filter_size num_hash N bfl hfuns a hnames ks s }} := by
  iintro Hks
  icases (BigSepL.bigSepL_pure (φ := fun (_ : ℕ) (k : ℕ) => k ≤ max_key) (l := ks)).1 $$ Hks
    with %Hks
  have Hks' : ∀ k ∈ ks, k ≤ max_key := by
    intro k Hk
    obtain ⟨i, Hi, rfl⟩ := List.mem_iff_getElem.1 Hk
    exact Hks i _ (List.getElem?_eq_getElem Hi)
  iintro !> %Φ Herr HΦ
  unfold init_bloom_filter
  wp_pures
  -- Rocq: `set (Ψ := ..)`
  let Ψ : List val → IProp GF := fun l => iprop(⌜num_hash < l.length⌝ ∨
    (∃ s : Finset ℕ,
      ↯ (fp_error filter_size num_hash ((num_hash - l.length) * ks.length) s.card) ∗
      ⌜∀ x : ℕ, x ∈ s → x < filter_size + 1⌝ ∗
      ([∗list] f ∈ l, ∃ γ,
        c.conhashfun γ filter_size f ∗
        ([∗list] k ∈ (List.range (max_key + 1)).filter (· ∉ ks), c.hashkey γ k none) ∗
        ([∗list] k ∈ ks, ∃ v, ⌜v ∈ s⌝ ∗ c.hashkey γ k (some v)))))
  wp_bind (App (App (App (Val list_seq_fun) _) _) _)
  wp_apply wp_list_seq_fun_HO_invariant Ψ 0 num_hash _ (fun _ _ => iprop(True)) $$ [] [Herr]
    with %hfuns %fαs ⟨%Hhfuns, %Hlen, HΨ, -⟩
  · iintro %i %l !> %Ξ HΨ HΞ
    wp_pures
    iapply pgl_wp_state_update
    wp_apply c.conhash_init filter_size max_key $$ [] with %γ %f ⟨#Hhinv, Hkeys⟩
    · itrivial
    icases keys_split max_key ks Hndup Hks' _ $$ Hkeys with ⟨Hks, Hrest⟩
    iapply HΞ
    isplitl
    · -- the invariant `Ψ`
      simp only [Ψ, List.length_cons]
      by_cases Haux : num_hash ≤ l.length
      · imodintro
        ileft
        ipureintro
        omega
      icases HΨ with (%H | ⟨%s, Herr, %Hbound, Hl⟩)
      · imodintro
        ileft
        ipureintro
        omega
      rw [show (num_hash - l.length) * ks.length =
          (num_hash - (l.length + 1)) * ks.length + ks.length by
        rw [← Nat.succ_mul, show (num_hash - (l.length + 1)).succ = num_hash - l.length by
          omega]]
      imod hash_preview_list filter_size num_hash _ ks f γ s Hbound $$ Hhinv %Hndup Hks Herr
        with ⟨%res, %Hres, Herr, Hks⟩
      imodintro
      iright
      iexists s ∪ res
      iframe Herr
      isplitr
      · ipureintro; exact Hres
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hrest Hks]
      · iexists γ
        iframe
        iexact Hhinv
      iapply BigSepL.bigSepL_mono_of_forall (Φ := fun _ (f : val) => iprop(∃ γ,
        c.conhashfun γ filter_size f ∗
        ([∗list] k ∈ (List.range (max_key + 1)).filter (· ∉ ks), c.hashkey γ k none) ∗
        ([∗list] k ∈ ks, ∃ v, ⌜v ∈ s⌝ ∗ c.hashkey γ k (some v)))) ?_ $$ Hl
      intro _ f'
      iintro ⟨%γ', Hf, Hr, Hks'⟩
      iexists γ'
      iframe Hf Hr
      iapply BigSepL.bigSepL_mono_of_forall
        (Φ := fun _ (k : ℕ) => iprop(∃ v, ⌜v ∈ s⌝ ∗ c.hashkey γ' k (some v))) ?_ $$ Hks'
      intro _ k
      iintro ⟨%v, %Hv, Hk⟩
      iexists v
      iframe Hk
      ipureintro
      exact Finset.mem_union_left _ Hv
    · itrivial
  · -- Rocq: `iRight; iExists ∅`
    simp only [Ψ, List.length_nil, Nat.sub_zero]
    iright
    iexists ∅
    rw [Finset.card_empty]
    iframe Herr
    isplitr
    · ipureintro; simp
    iapply BigSepL.bigSepL_nil.2
    iempintro
  wp_pures
  have Hf : ⊢@{IProp GF} [∗list] i ∈ List.range (((filter_size + 1 : ℕ) : ℤ)).toNat,
      WP (cpl(v(λ x, #false) #(i : ℕ))) {{ v, ⌜v = LitV (LitBool false)⌝ }} := by
    refine BigSepL.bigSepL_intro (P := iprop(emp)) (fun k x _ => ?_)
    iintro -
    wp_pures
    ipureintro
    rfl
  wp_apply wp_array_init (Q := fun _ v => iprop(⌜v = LitV (LitBool false)⌝))
    (((filter_size + 1 : ℕ) : ℤ)) _ (by omega) $$ [] with %a %arr ⟨%HlenA, Ha, Harr⟩
  · iapply Hf
  wp_pures
  wp_alloc l as Hl
  wp_pures
  icases (BigSepL.bigSepL_pure (φ := fun (_ : ℕ) (v : val) => v = LitV (LitBool false))
    (l := arr)).1 $$ Harr with %Harr'
  simp only [Ψ]
  icases HΨ with (%H | ⟨%s, Herr, %Hbound, Hfs⟩)
  · omega
  icases big_sepL_exists (fun _ γ (f : val) => iprop(
      c.conhashfun γ filter_size f ∗
      ([∗list] k ∈ (List.range (max_key + 1)).filter (· ∉ ks), c.hashkey γ k none) ∗
      ([∗list] k ∈ ks, ∃ v, ⌜v ∈ s⌝ ∗ c.hashkey γ k (some v)))) fαs $$ Hfs
    with ⟨%hnames, Hfs⟩
  rw [Hlen, Nat.sub_self, Nat.zero_mul]
  -- Rocq: `iAssert (.. ∗ [∗ list] γ ∈ hnames, ..)` via `big_sepL2_sep_sepL_r`
  ihave ⟨Hrest, Hinvs⟩ := (BigSepL2.bigSepL2_sep_sepL_right
    (Φ := fun _ γ => iprop([∗list] k ∈ (List.range (max_key + 1)).filter (· ∉ ks),
      c.hashkey γ k none))
    (Ψ := fun _ (f : val) γ => iprop(c.conhashfun γ filter_size f ∗
      ([∗list] k ∈ ks, ∃ v, ⌜v ∈ s⌝ ∗ c.hashkey γ k (some v))))
    (l1 := fαs) (l2 := hnames)).1 $$ [Hfs]
  · iapply BigSepL2.bigSepL2_mono_of_forall ?_ $$ Hfs
    intro _ f γ
    iintro ⟨Hf, Hr, Hks⟩
    iframe
  have HlenA' : arr.length = filter_size + 1 := by omega
  imod inv_alloc (N.@"bf") ⊤
    (bloom_filter_inv_aux filter_size num_hash l hfuns a hnames ks s) $$ [Hl Ha Hinvs] with #Hinv
  · inext
    unfold bloom_filter_inv_aux
    iexists fαs
    iframe Hl
    isplitr
    · ipureintro; exact Hhfuns
    isplitr
    · ipureintro; exact Hlen
    isplitl [Hinvs]
    · unfold con_hash_inv_list
      iexact Hinvs
    isplitr
    · ipureintro; exact Hbound
    iexists arr
    iframe Ha
    ipureintro
    refine ⟨HlenA', ?_, ?_⟩
    · intro i Hi
      right
      obtain ⟨x, Hx⟩ : ∃ x, arr[i]? = some x :=
        ⟨arr[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      rw [Hx, Harr' i x Hx]
    · intro i _ Hi
      have := Harr' i _ Hi
      simp at this
  imodintro
  iapply HΦ
  iexists hfuns, a, hnames, s
  iframe Herr Hrest
  unfold bloom_filter_inv
  iexact Hinv

end conc_bloom_filter

end Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt
