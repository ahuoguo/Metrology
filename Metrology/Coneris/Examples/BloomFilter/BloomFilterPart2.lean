module

public import Metrology.Coneris.Examples.BloomFilter.BloomFilter

/-!
# A (sequential) Bloom filter, part 2: initialization

Ported from clutch/theories/coneris/examples/bloom_filter/bloom_filter.v
(`bloom_filter_init_spec`). See `Coneris.Examples.BloomFilter.BloomFilter` for the name map.

## Rocq → Lean map
* `bloom_filter_init_spec`: same name. `RET #l` is `RET LitV (LitLoc l)`.
* The `iInduction num_hash` proving `[∗ list] h;m ∈ vs;repeat ∅ num_hash, hashfun ..` from
  `[∗ list] k↦v ∈ vs, hashfun .. v ∅` is iris-lean's `bigSepL2_replicate_right` (after
  substituting `num_hash = length vs`); the Lean `induction num_hash` for the `Forall` goal is
  `List.mem_replicate`.
* The premise `[∗ list] i ∈ seq 0 n, WP f #i {{ Q i }}` of `wp_array_init` is proved with
  iris-lean's `bigSepL_intro` (Rocq: `big_sepL_intro`).

## Added
* `hmap_dom_empty` (stdpp's `dom_empty_L`).
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

/-- Rocq (stdpp): `dom_empty_L`. -/
theorem hmap_dom_empty : hmap_dom (∅ : hmap) = ∅ := by
  ext x
  rw [mem_hmap_dom]
  simp

/-- Rocq: `bloom_filter_init_spec`. -/
theorem bloom_filter_init_spec (rem : ℕ) :
    {{ ↯ (fp_error filter_size num_hash (num_hash * rem) 0) }}
      cpl(&(init_bloom_filter filter_size num_hash) #())
    {{ (l : Loc), RET LitV (LitLoc l);
        (is_bloom_filter filter_size num_hash l ∅ rem : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold init_bloom_filter
  wp_pures
  wp_bind (App (App (App (Val list_seq_fun) _) _) _)
  wp_apply wp_list_seq_fun_HO 0 num_hash _ (fun _ v => hashfun filter_size v ∅) $$ []
    with %v %vs ⟨%Hvs, %Hlen, Hg⟩
  · iintro %i !> %Φ' - HΦ'
    wp_pures
    wp_apply wp_init_hash_basic filter_size ⊤ $$ [] with %f Hf
    · itrivial
    iapply HΦ'
    iexact Hf
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
  imodintro
  iapply HΦ
  icases (BigSepL.bigSepL_pure (φ := fun (_ : ℕ) (v : val) => v = LitV (LitBool false))
    (l := arr)).1 $$ Harr with %Harr'
  unfold is_bloom_filter
  iexists v, vs, List.replicate num_hash ∅, a, arr, ∅
  rw [Finset.card_empty]
  iframe
  isplitr
  · ipureintro; exact Hvs
  isplitr
  · ipureintro; exact Hlen
  isplitl [Hg]
  · subst Hlen
    iapply BigSepL2.bigSepL2_replicate_right.2
    iexact Hg
  ipureintro
  have HlenA' : arr.length = filter_size + 1 := by omega
  refine ⟨HlenA', by simp, ?_, ?_, by simp, by simp, ?_⟩
  · intro m Hm
    rw [List.eq_of_mem_replicate Hm, hmap_dom_empty]
  · intro e He; simp at He
  · intro i Hi _
    obtain ⟨x, Hx⟩ : ∃ x, arr[i]? = some x :=
      ⟨arr[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    rw [Hx, Harr' i x Hx]

end bloom_filter

end Coneris.Examples.BloomFilter.BloomFilter
