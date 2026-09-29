module

public import Metrology.Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt

/-!
# A concurrent Bloom filter, part 3: insertion

Ported from clutch/theories/coneris/examples/bloom_filter/concurrent_bloom_filter_alt.v
(`bloom_filter_insert_thread_spec`, `insert_bloom_filter_loop_spec`,
`insert_bloom_filter_loop_seq_spec`). See `Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt`
for the name map.

## Rocq → Lean map
* Same names. The Rocq statement `(k ∈ ks) -> ([∗ list] k ∈ ks, ⌜k ≤ max_key⌝) -∗ {{{ .. }}}`
  is kept as a pure hypothesis followed by `⊢ ([∗list] ..) -∗ {{ .. }} .. {{ .. }}`.
  `RET #()` is `RET LitV LitUnit`; `is_list ks ksv` is `Coneris.Lib.List.is_list`
  (for `ks : List ℕ`, via `Inject ℕ val`).
* Rocq's `#Hhinv` (a persistent copy of `con_hash_inv_list`, obtained from the invariant) uses
  the persistence of `conhashfun` and `hashkey γ k (Some n)`; in Lean this is the instance
  `con_hash_inv_list_persistent` (Added).
* `big_sepL_elem_of` is `BigSepL.bigSepL_mem`; `list_lookup_insert_eq`/`_ne` are
  `List.getElem?_set_self`/`List.getElem?_set_ne` (`<[v := #true]> arr` is `arr.set v ..`).
* `iInduction ks` is a Lean `induction ks` on the Texan-triple statements; `(Hks 0)`,
  `(Hks (S i))` are the corresponding instances of the pure hypothesis
  `∀ i x, ks[i]? = some x → x ∈ ns` (obtained by `BigSepL.bigSepL_pure`).
* `wp_par` is applied through the helper `wp_par'` (see part 1). Rocq's `do 2 wp_pure` is
  `wp_pure; wp_pure`. The induction hypothesis is stated for the constant
  `insert_bloom_filter_loop(_seq)`, which is unfolded (`unfold .. at IH'`) to match the
  substituted recursive call.

## Added
* `con_hash_inv_list_persistent` (see above).
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

namespace Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt

section conc_bloom_filter

variable (filter_size max_key num_hash : ℕ)
variable {GF : BundledGFunctors} [conerisGS GF] [c : con_hash4 GF]

/-- `con_hash_inv_list` is persistent (Rocq: found by instance search through the
definition). -/
instance con_hash_inv_list_persistent (hfs : List val) (hnames : List (GName × GName × GName))
    (ks : List ℕ) (s : Finset ℕ) :
    Persistent (con_hash_inv_list filter_size hfs hnames ks s (c := c)) := by
  unfold con_hash_inv_list
  infer_instance

/-- Rocq: `bloom_filter_insert_thread_spec`. -/
theorem bloom_filter_insert_thread_spec (N : Namespace) (bfl : Loc) (hfuns : val) (a : Loc)
    (hnames : List (GName × GName × GName)) (k : ℕ) (ks : List ℕ) (s : Finset ℕ)
    (Hk : k ∈ ks) :
    ⊢ ([∗list] k ∈ ks, ⌜k ≤ max_key⌝) -∗
      {{ bloom_filter_inv filter_size num_hash N bfl hfuns a hnames ks s (c := c) }}
        cpl(&insert_bloom_filter #bfl #k)
      {{ RET LitV LitUnit; True }} := by
  iintro -
  iintro !> %Φ #Hinv HΦ
  unfold insert_bloom_filter
  wp_pures
  wp_bind (Load _)
  unfold bloom_filter_inv
  iinv Hinv with ⟨%hfs, >Hbfl, >%Hhfs, >%Hlen, #Hhinv, >%Hbound, Harr⟩ Hclose
  wp_load
  imod Hclose $$ [Hbfl Harr]
  · inext
    unfold bloom_filter_inv_aux
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
  wp_apply wp_list_iter_invariant_HO
      (fun _ fs2 => iprop(∃ hnames2, con_hash_inv_list filter_size fs2 hnames2 ks s)) hfs _ hfuns
    $$ [] [] with -
  · iintro %fs1 %f %fs2 !> %Ψ ⟨%hnames2, Hiter⟩ HΨ
    wp_pures
    icases con_hash_inv_list_cons filter_size f fs2 hnames2 ks s $$ Hiter
      with ⟨%γ, %hnames3, -, #Hinvf, Hfrags, Htail⟩
    icases BigSepL.bigSepL_mem (Φ := fun k => iprop(∃ n, ⌜n ∈ s⌝ ∗ c.hashkey γ k (some n)))
      Hk $$ Hfrags with ⟨%v, %Hv, #Hfrag⟩
    wp_apply c.wp_conhashfun_prev f k v γ filter_size $$ [] with -
    · iframe Hinvf Hfrag
    wp_pures
    iinv Hinv with ⟨%hfs', Hbfl, Hhfs', Hlen', Hhinv', >%Hbound', %arr, Harr, >%HlenA, >%Htf,
      >%Htrue⟩ Hclose
    have Hvlt : v < filter_size + 1 := Hbound' v Hv
    wp_apply wp_store_offset a v arr (LitV (LitBool true))
      ⟨arr[v]'(by omega), List.getElem?_eq_getElem (by omega)⟩ $$ Harr with Harr
    imod Hclose $$ [Hbfl Hhfs' Hlen' Hhinv' Harr]
    · inext
      unfold bloom_filter_inv_aux
      iexists hfs'
      iframe Hbfl Hhfs' Hlen' Hhinv'
      isplitr
      · ipureintro; exact Hbound'
      iexists arr.set v (LitV (LitBool true))
      iframe Harr
      ipureintro
      refine ⟨by rw [List.length_set, HlenA], ?_, ?_⟩
      · intro i Hi
        by_cases Hiv : i = v
        · subst Hiv
          left
          rw [List.getElem?_set_self (by omega)]
        · rw [List.getElem?_set_ne (fun h => Hiv h.symm)]
          exact Htf i Hi
      · intro i Hi Hlookup
        by_cases Hiv : i = v
        · subst Hiv; exact Hv
        · rw [List.getElem?_set_ne (fun h => Hiv h.symm)] at Hlookup
          exact Htrue i Hi Hlookup
    imodintro
    iapply HΨ
    iexists hnames3
    iexact Htail
  · isplitr
    · ipureintro; exact Hhfs
    iexists hnames
    iexact Hhinv
  iapply HΦ
  itrivial

/-- Rocq: `insert_bloom_filter_loop_spec`. -/
theorem insert_bloom_filter_loop_spec [spawnG GF] (N : Namespace) (bfl : Loc) (hfuns : val)
    (a : Loc) (hnames : List (GName × GName × GName)) (s : Finset ℕ) (ns ks : List ℕ)
    (ksv : val) (Hksv : is_list ks ksv) :
    {{ bloom_filter_inv filter_size num_hash N bfl hfuns a hnames ns s (c := c) ∗
        ([∗list] k ∈ ks, ⌜k ∈ ns⌝) ∗
        ([∗list] k ∈ ns, ⌜k ≤ max_key⌝) }}
      cpl(&insert_bloom_filter_loop #bfl &ksv)
    {{ v, RET v; True }} := by
  induction ks generalizing ksv with
  | nil =>
    iintro %Φ ⟨#Hinv, -, -⟩ HΦ
    simp only [is_list] at Hksv
    subst Hksv
    unfold insert_bloom_filter_loop
    wp_pures
    iapply HΦ
    itrivial
  | cons k ks' IH =>
    iintro %Φ ⟨#Hinv, #Hks, #Hns⟩ HΦ
    obtain ⟨kv, rfl, Htail⟩ := Hksv
    icases (BigSepL.bigSepL_pure (φ := fun (_ : ℕ) (k : ℕ) => k ∈ ns) (l := k :: ks')).1 $$ Hks
      with %Hks'
    unfold insert_bloom_filter_loop
    wp_pures
    wp_apply wp_par' (fun _ => iprop(True)) (fun _ => iprop(True)) $$ [] [] with %v1 %v2 -
    · wp_apply bloom_filter_insert_thread_spec filter_size max_key num_hash N bfl hfuns a hnames
        k ns s (Hks' 0 k rfl) $$ Hns Hinv with -
      itrivial
    · have IH' := IH kv Htail
      unfold insert_bloom_filter_loop at IH'
      wp_apply IH' $$ [] with %v -
      · isplitr
        · iexact Hinv
        isplitr
        · iapply (BigSepL.bigSepL_pure (φ := fun (_ : ℕ) (k : ℕ) => k ∈ ns) (l := ks')).2
          ipureintro
          intro i x Hx
          exact Hks' (i + 1) x Hx
        iexact Hns
      itrivial
    inext
    iapply HΦ
    itrivial

/-- Rocq: `insert_bloom_filter_loop_seq_spec`. -/
theorem insert_bloom_filter_loop_seq_spec (N : Namespace) (bfl : Loc) (hfuns : val)
    (a : Loc) (hnames : List (GName × GName × GName)) (s : Finset ℕ) (ns ks : List ℕ)
    (ksv : val) (Hksv : is_list ks ksv) :
    {{ bloom_filter_inv filter_size num_hash N bfl hfuns a hnames ns s (c := c) ∗
        ([∗list] k ∈ ks, ⌜k ∈ ns⌝) ∗
        ([∗list] k ∈ ns, ⌜k ≤ max_key⌝) }}
      cpl(&insert_bloom_filter_loop_seq #bfl &ksv)
    {{ v, RET v; True }} := by
  induction ks generalizing ksv with
  | nil =>
    iintro %Φ ⟨#Hinv, -, -⟩ HΦ
    simp only [is_list] at Hksv
    subst Hksv
    unfold insert_bloom_filter_loop_seq
    wp_pures
    iapply HΦ
    itrivial
  | cons k ks' IH =>
    iintro %Φ ⟨#Hinv, #Hks, #Hns⟩ HΦ
    obtain ⟨kv, rfl, Htail⟩ := Hksv
    icases (BigSepL.bigSepL_pure (φ := fun (_ : ℕ) (k : ℕ) => k ∈ ns) (l := k :: ks')).1 $$ Hks
      with %Hks'
    unfold insert_bloom_filter_loop_seq
    wp_pures
    wp_bind (App (App (Val insert_bloom_filter) _) _)
    wp_apply bloom_filter_insert_thread_spec filter_size max_key num_hash N bfl hfuns a hnames
      k ns s (Hks' 0 k rfl) $$ Hns Hinv with -
    wp_pure
    wp_pure
    have IH' := IH kv Htail
    unfold insert_bloom_filter_loop_seq at IH'
    iapply IH' $$ [] [HΦ]
    · isplitr
      · iexact Hinv
      isplitr
      · iapply (BigSepL.bigSepL_pure (φ := fun (_ : ℕ) (k : ℕ) => k ∈ ns) (l := ks')).2
        ipureintro
        intro i x Hx
        exact Hks' (i + 1) x Hx
      iexact Hns
    inext
    iexact HΦ

end conc_bloom_filter

end Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt
