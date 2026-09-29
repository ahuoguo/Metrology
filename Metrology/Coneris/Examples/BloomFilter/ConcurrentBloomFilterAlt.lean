module

public import Metrology.Coneris.Examples.HashDir.ConHashInterface4
public import Metrology.Coneris.Examples.BloomFilter.BloomFilterPart3
public import Metrology.Coneris.Lib.ListHO
public import Metrology.Coneris.Lib.Array
public import Metrology.Coneris.Lib.Par

/-!
# A concurrent Bloom filter

Ported from clutch/theories/coneris/examples/bloom_filter/concurrent_bloom_filter_alt.v
(part 1: the programs, the invariant and `hash_preview_list`). The specs are in
`ConcurrentBloomFilterAltPart2` (`bloom_filter_init_spec`), `ConcurrentBloomFilterAltPart3`
(`bloom_filter_insert_thread_spec`, `insert_bloom_filter_loop_spec`,
`insert_bloom_filter_loop_seq_spec`) and `ConcurrentBloomFilterAltPart4`
(`bloom_filter_lookup_spec`, `main_bloom_filter_seq_spec`).

## Rocq → Lean map
* Namespace `Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt` (for all four modules).
  All Rocq names are kept: `init_bloom_filter`, `insert_bloom_filter`, `lookup_bloom_filter`,
  `insert_bloom_filter_loop`, `main_bloom_filter`, `insert_bloom_filter_loop_seq`,
  `main_bloom_filter_seq`, `con_hash_inv_list`, `con_hash_inv_list_cons`,
  `bloom_filter_inv_aux`, `bloom_filter_inv`, `hash_preview_list`, `bloom_filter_init_spec`,
  `bloom_filter_insert_thread_spec`, `bloom_filter_lookup_spec`,
  `insert_bloom_filter_loop_spec`, `insert_bloom_filter_loop_seq_spec`,
  `main_bloom_filter_seq_spec`.
  `fp_error` (and its lemmas) are those of `Coneris.Examples.BloomFilter.BloomFilter`
  (Rocq: `Require Import bloom_filter`); they are opened selectively since the sequential
  Bloom filter's programs have the same names as the ones here.
* The section variables `filter_size max_key num_hash` are explicit arguments (only of the
  declarations that use them). The context `conerisGS Σ, spawnG Σ, c : con_hash4 Σ` is
  `[conerisGS GF] [spawnG GF] [c : con_hash4 GF]` (`spawnG` only where `|||` is used). The
  unused context items `inG Σ (excl_authR boolO)`, `inG Σ (prodR fracR val0)` are dropped
  (no statement or proof of the file mentions them).
* `init_con_hash` is the class field `c.init_con_hash`, so `init_bloom_filter`
  and `main_bloom_filter(_seq)` depend on the `con_hash4` instance.
* Programs are transcribed with the `cpl`/`cpl_val` notation; Rocq's string binder `"_"` is
  kept as `"_"`. `e1 ||| e2` (in expression scope, i.e. `par (λ: <>, e1)%E (λ: <>, e2)%E`) is
  the local notation `e1 ‖ e2` (as in `Coneris.Examples.ParallelAdd`), and `wp_par` is applied
  through the local helper `wp_par'` (`par_V` unfolded).
* `gset nat` is `Finset ℕ`, `size` is `Finset.card`, `list_to_set`/`∈` on lists are list
  membership; `arr !! i` is `arr[i]?`; `hnames` is a `List (GName × GName × GName)` (the
  `con_hash4` ghost names).
* `[∗ list] i ↦ f;γ ∈ hfs;hnames, ..` (index unused) is `[∗list] f;γ ∈ hfs;hnames, ..`.
* `[∗ set] k ∈ (set_seq 0 (S max_key) ∖ list_to_set ks), P k` is
  `[∗list] k ∈ (List.range (max_key + 1)).filter (· ∉ ks), P k`: iris-lean has no big
  separating conjunction over `Finset`s, and the filtered list is duplicate-free with exactly
  the elements of that set (as in `ConHashInterface4.conhash_init`, which uses
  `List.range (max + 1)` for `set_seq 0 (S max)`).
* `nonnegreal`s `mknonnegreal (fp_error ..) _` are the `ℝ≥0∞` values `fp_error ..`.
* `bfl ↦ (hfuns, LitV (LitLoc a))%V` is `bfl ↦ PairV hfuns (LitV (LitLoc a))`;
  `N.@"bf"` is `N.@"bf"`.

## Added
* `presample_step`: the error inequality given to `hashkey_presample` in
  `hash_preview_list` (Rocq: proved inline by `case_bool_decide`, `fp_error_max` and real
  arithmetic). In `ℝ≥0∞` the truncated subtraction `filter_size + 1 - size bad` does not
  truncate since `size bad ≤ filter_size + 1` (all elements of `bad` are `< filter_size + 1`).
* `bloom_filter_inv_persistent` (Rocq: found by instance search through `inv`).
* Sanity checks (`example`) of the program ASTs.

## Deviations
* `bloom_filter_inv_aux` is an `abbrev` (Rocq: `Definition`), so that `iinv` can destruct the
  invariant body directly (Rocq's `iInv` sees through the definition).
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

/-- `e1 ||| e2` (Rocq: `par (λ: <>, e1)%E (λ: <>, e2)%E` in `expr_scope`) as a program
notation. -/
scoped syntax:55 cpl_exp:56 " ‖ " cpl_exp:55 : cpl_exp

macro_rules
  | `(cpl($e1 ‖ $e2)) => `(cpl(&par (λ <>, $e1) (λ <>, $e2)))

/-- Helper (not in Rocq): `wp_par` with `par_V` unfolded, so that `wp_apply` finds it. -/
theorem wp_par' {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]
    (Ψ1 Ψ2 : val → IProp GF) (e1 e2 : expr) (Φ : val → IProp GF) :
    ⊢ WP e1 {{ Ψ1 }} -∗ WP e2 {{ Ψ2 }} -∗
      (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (PairV v1 v2)) -∗
      WP cpl(&par v(λ <>, &e1) v(λ <>, &e2)) {{ Φ }} :=
  wp_par Ψ1 Ψ2 e1 e2 Φ

section conc_bloom_filter

variable (filter_size max_key num_hash : ℕ)
variable {GF : BundledGFunctors} [conerisGS GF] [c : con_hash4 GF]

/-! ## Programs -/

/-- Rocq: `init_bloom_filter`. -/
def init_bloom_filter : val :=
  cpl_val(λ "_",
    let hfuns := &list_seq_fun #(0 : ℕ) #num_hash
      (λ "_", &c.init_con_hash #filter_size #max_key) in
    let arr := &array_init #(filter_size + 1 : ℕ) (λ x, #false) in
    let l := ref((hfuns, arr)) in
    l)

/-- Rocq: `insert_bloom_filter`. -/
def insert_bloom_filter : val :=
  cpl_val(λ l v,
    let (hfuns, arr) := !l;
    &list_iter (λ h,
        let i := h v in
        arr +ₗ i ← #true) hfuns)

/-- Rocq: `lookup_bloom_filter`. -/
def lookup_bloom_filter : val :=
  cpl_val(λ l v,
    let (hfuns, arr) := !l;
    let res := ref(#true) in
    &list_iter (λ h,
        let i := h v in
        if !(arr +ₗ i) then #() else res ← #false) hfuns;
    !res)

/-- Rocq: `insert_bloom_filter_loop`. -/
def insert_bloom_filter_loop : val :=
  cpl_val(rec aux bfl ks :=
    match ks with
    | none() => #()
    | some(p) =>
        let h := fst(p) in
        let t := snd(p) in
        (&insert_bloom_filter bfl h) ‖ (aux bfl t))

/-- Rocq: `main_bloom_filter`. -/
def main_bloom_filter (ksv ktest : val) : expr :=
  cpl(let bfl := &(init_bloom_filter filter_size max_key num_hash (c := c)) #() in
    &insert_bloom_filter_loop bfl &ksv;
    &lookup_bloom_filter bfl &ktest)

/-- Rocq: `insert_bloom_filter_loop_seq`. -/
def insert_bloom_filter_loop_seq : val :=
  cpl_val(rec aux bfl ks :=
    match ks with
    | none() => #()
    | some(p) =>
        let h := fst(p) in
        let t := snd(p) in
        (&insert_bloom_filter bfl h); (aux bfl t))

/-- Rocq: `main_bloom_filter_seq`. -/
def main_bloom_filter_seq (ksv ktest : val) : expr :=
  cpl(let bfl := &(init_bloom_filter filter_size max_key num_hash (c := c)) #() in
    &insert_bloom_filter_loop_seq bfl &ksv;
    &lookup_bloom_filter bfl &ktest)

/-- Sanity check: the transcription of `lookup_bloom_filter` (the sequencing `;;` is inside
the `let: "res"`). -/
example : lookup_bloom_filter =
    RecV .BAnon (.BNamed "l") (expr.Rec .BAnon (.BNamed "v")
      (App (expr.Rec .BAnon (.BNamed "arr")
        (App (expr.Rec .BAnon (.BNamed "hfuns")
          (App (expr.Rec .BAnon (.BNamed "arr")
            (App (expr.Rec .BAnon (.BNamed "res")
              (App (expr.Rec .BAnon .BAnon (Load (Var "res")))
                (App (App (Val list_iter)
                  (expr.Rec .BAnon (.BNamed "h")
                    (App (expr.Rec .BAnon (.BNamed "i")
                      (If (Load (BinOp .OffsetOp (Var "arr") (Var "i")))
                        (Val (LitV LitUnit))
                        (Store (Var "res") (Val (LitV (LitBool false))))))
                      (App (Var "h") (Var "v")))))
                  (Var "hfuns"))))
              (Alloc (Val (LitV (LitBool true))))))
            (Snd (Var "arr"))))
          (Fst (Var "arr"))))
        (Load (Var "l")))) :=
  rfl

/-- Sanity check: the transcription of `insert_bloom_filter_loop`. -/
example : insert_bloom_filter_loop =
    RecV (.BNamed "aux") (.BNamed "bfl") (expr.Rec .BAnon (.BNamed "ks")
      (Case (Var "ks")
        (expr.Rec .BAnon .BAnon (Val (LitV LitUnit)))
        (expr.Rec .BAnon (.BNamed "p")
          (App (expr.Rec .BAnon (.BNamed "h")
            (App (expr.Rec .BAnon (.BNamed "t")
              (App (App (Val par)
                  (expr.Rec .BAnon .BAnon
                    (App (App (Val insert_bloom_filter) (Var "bfl")) (Var "h"))))
                (expr.Rec .BAnon .BAnon (App (App (Var "aux") (Var "bfl")) (Var "t")))))
              (Snd (Var "p"))))
            (Fst (Var "p")))))) :=
  rfl

/-- Sanity check: the transcription of `main_bloom_filter_seq`. -/
example (ksv ktest : val) : main_bloom_filter_seq filter_size max_key num_hash ksv ktest =
    App (expr.Rec .BAnon (.BNamed "bfl")
        (App (expr.Rec .BAnon .BAnon
            (App (App (Val lookup_bloom_filter) (Var "bfl")) (Val ktest)))
          (App (App (Val insert_bloom_filter_loop_seq) (Var "bfl")) (Val ksv))))
      (App (Val (init_bloom_filter filter_size max_key num_hash (c := c)))
        (Val (LitV LitUnit))) :=
  rfl

/-! ## Invariants -/

/-- Rocq: `con_hash_inv_list`. -/
def con_hash_inv_list (hfs : List val) (hnames : List (GName × GName × GName)) (ks : List ℕ)
    (s : Finset ℕ) : IProp GF :=
  iprop([∗list] f;γ ∈ hfs;hnames,
    c.conhashfun γ filter_size f ∗
    ([∗list] k ∈ ks, ∃ n, ⌜n ∈ s⌝ ∗ c.hashkey γ k (some n)))

/-- Rocq: `con_hash_inv_list_cons`. -/
theorem con_hash_inv_list_cons (f : val) (fs2 : List val) (hnames : List (GName × GName × GName))
    (ks : List ℕ) (s : Finset ℕ) :
    con_hash_inv_list filter_size (f :: fs2) hnames ks s ⊢@{IProp GF}
      ∃ γ hnames2,
        ⌜hnames = γ :: hnames2⌝ ∗
        c.conhashfun γ filter_size f ∗
        ([∗list] k ∈ ks, ∃ n, ⌜n ∈ s⌝ ∗ c.hashkey γ k (some n)) ∗
        con_hash_inv_list filter_size fs2 hnames2 ks s := by
  unfold con_hash_inv_list
  cases hnames with
  | nil =>
    iintro H
    ihave %Hlen := BigSepL2.bigSepL2_length $$ H
    simp at Hlen
  | cons γ hnames2 =>
    iintro ⟨⟨Hf, Hks⟩, Htail⟩
    iexists γ, hnames2
    iframe
    ipureintro
    rfl

/-- Rocq: `bloom_filter_inv_aux`. (An `abbrev`, so that `iinv` destructs it.) -/
abbrev bloom_filter_inv_aux (bfl : Loc) (hfuns : val) (a : Loc)
    (hnames : List (GName × GName × GName)) (ks : List ℕ) (s : Finset ℕ) : IProp GF :=
  iprop(∃ hfs : List val,
    bfl ↦ PairV hfuns (LitV (LitLoc a)) ∗
    ⌜is_list_HO hfs hfuns⌝ ∗
    ⌜hfs.length = num_hash⌝ ∗
    con_hash_inv_list filter_size hfs hnames ks s ∗
    ⌜∀ i, i ∈ s → i < filter_size + 1⌝ ∗
    (∃ arr : List val,
      (a ↦∗ arr) ∗
      ⌜arr.length = filter_size + 1⌝ ∗
      ⌜∀ i, i < filter_size + 1 →
        arr[i]? = some (LitV (LitBool true)) ∨ arr[i]? = some (LitV (LitBool false))⌝ ∗
      ⌜∀ i, i < filter_size + 1 → arr[i]? = some (LitV (LitBool true)) → i ∈ s⌝))

/-- Rocq: `bloom_filter_inv`. -/
def bloom_filter_inv (N : Namespace) (bfl : Loc) (hfuns : val) (a : Loc)
    (hnames : List (GName × GName × GName)) (ks : List ℕ) (s : Finset ℕ) : IProp GF :=
  inv (N.@"bf") (bloom_filter_inv_aux filter_size num_hash bfl hfuns a hnames ks s)

instance bloom_filter_inv_persistent (N : Namespace) (bfl : Loc) (hfuns : val) (a : Loc)
    (hnames : List (GName × GName × GName)) (ks : List ℕ) (s : Finset ℕ) :
    Persistent (bloom_filter_inv filter_size num_hash N bfl hfuns a hnames ks s (c := c)) := by
  unfold bloom_filter_inv
  infer_instance

/-! ## Presampling the hashes of a list of keys -/

/-- The error inequality of one presampling step of `hash_preview_list` (Rocq: proved inline
by `case_bool_decide`, `fp_error_max` and real arithmetic). -/
theorem presample_step (K : ℕ) (bad : Finset ℕ) (Hbound : ∀ x, x ∈ bad → x < filter_size + 1) :
    fp_error filter_size num_hash K bad.card * bad.card +
      fp_error filter_size num_hash K (bad.card + 1) *
        ((filter_size : ℝ≥0∞) + 1 - bad.card) ≤
      fp_error filter_size num_hash (K + 1) bad.card * ((filter_size : ℝ≥0∞) + 1) := by
  have Hcard : bad.card ≤ filter_size + 1 := by
    have Hsub : bad ⊆ Finset.range (filter_size + 1) := fun x Hx =>
      Finset.mem_range.2 (Hbound x Hx)
    simpa using Finset.card_le_card Hsub
  rw [fp_error_step _ _ _ _ Hcard, ENNReal.div_add_div_same,
    ENNReal.div_mul_cancel (by simp) (by simp)]

/-- Rocq: `hash_preview_list`. -/
theorem hash_preview_list (rem : ℕ) (ks : List ℕ) (f : val) (γs : GName × GName × GName)
    (bad : Finset ℕ) (Hbound : ∀ x : ℕ, x ∈ bad → x < filter_size + 1) :
    ⊢ c.conhashfun γs filter_size f -∗
      ⌜ks.Nodup⌝ -∗
      ([∗list] k ∈ ks, c.hashkey γs k none) -∗
      ↯ (fp_error filter_size num_hash (rem + ks.length) bad.card) -∗
      state_update ⊤ ⊤ iprop(∃ res : Finset ℕ,
        ⌜∀ x : ℕ, x ∈ bad ∪ res → x < filter_size + 1⌝ ∗
        ↯ (fp_error filter_size num_hash rem (bad ∪ res).card) ∗
        ([∗list] k ∈ ks, ∃ n, ⌜n ∈ bad ∪ res⌝ ∗ c.hashkey γs k (some n))) := by
  induction ks generalizing bad with
  | nil =>
    iintro #Hhinv %Hndup Hnone Herr
    simp only [List.length_nil, Nat.add_zero]
    imodintro
    iexists bad
    rw [Finset.union_self]
    iframe
    isplitr
    · ipureintro; exact Hbound
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons k ks IH =>
    iintro #Hhinv %Hndup ⟨Hknone, Hksnone⟩ Herr
    have Hdup2 : ks.Nodup := (List.nodup_cons.1 Hndup).2
    simp only [List.length_cons]
    rw [show rem + (ks.length + 1) = (rem + ks.length) + 1 by omega]
    imod c.hashkey_presample k bad _
      (fp_error filter_size num_hash (rem + ks.length) bad.card)
      (fp_error filter_size num_hash (rem + ks.length) (bad.card + 1)) γs filter_size f
      Hbound (presample_step filter_size num_hash _ bad Hbound) $$ Hhinv Hknone Herr
      with ⟨%v, (⟨%Hnotbad, Herr⟩ | ⟨%Hbad, Herr⟩), #Hhauth⟩
    · -- `v ∉ bad`: the new bad set is `bad ∪ {v}`
      have Hbound' : ∀ x : ℕ, x ∈ bad ∪ {(v : ℕ)} → x < filter_size + 1 := by
        intro x Hx
        rw [Finset.mem_union, Finset.mem_singleton] at Hx
        rcases Hx with Hx | rfl
        · exact Hbound x Hx
        · exact v.isLt
      rw [show bad.card + 1 = (bad ∪ {(v : ℕ)}).card by
        rw [Finset.card_union_of_disjoint (by simpa using Hnotbad), Finset.card_singleton]]
      imod IH (bad ∪ {(v : ℕ)}) Hbound' $$ Hhinv %Hdup2 Hksnone Herr
        with ⟨%res, %Hres, Herr, Hks⟩
      imodintro
      iexists (bad ∪ {(v : ℕ)}) ∪ res
      rw [show bad ∪ (bad ∪ {(v : ℕ)} ∪ res) = bad ∪ {(v : ℕ)} ∪ res by
        rw [← Finset.union_assoc, ← Finset.union_assoc, Finset.union_self]]
      iframe Herr Hks
      isplitr
      · ipureintro; exact Hres
      iexists (v : ℕ)
      iframe Hhauth
      ipureintro
      simp
    · -- `v ∈ bad`: the bad set is unchanged
      imod IH bad Hbound $$ Hhinv %Hdup2 Hksnone Herr with ⟨%res, %Hres, Herr, Hks⟩
      imodintro
      iexists bad ∪ res
      rw [show bad ∪ (bad ∪ res) = bad ∪ res by
        rw [← Finset.union_assoc, Finset.union_self]]
      iframe Herr Hks
      isplitr
      · ipureintro; exact Hres
      iexists (v : ℕ)
      iframe Hhauth
      ipureintro
      exact Finset.mem_union_left _ Hbad

end conc_bloom_filter

end Coneris.Examples.BloomFilter.ConcurrentBloomFilterAlt
