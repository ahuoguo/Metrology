module

public import Metrology.Coneris.Examples.Hash
public import Metrology.Coneris.Lib.ListHO
public import Metrology.Coneris.Lib.Array

/-!
# A (sequential) Bloom filter

Ported from clutch/theories/coneris/examples/bloom_filter/bloom_filter.v (part 1: the false
positive error `fp_error`, the programs, the representation predicates `is_bloom_filter`,
`is_bloom_filter_partial` and the conversions between them). The specs are in
`BloomFilterPart2` (`bloom_filter_init_spec`), `BloomFilterPart3` (`bloom_filter_insert_spec`)
and `BloomFilterPart4` (`bloom_filter_lookup_in_spec`, `bloom_filter_lookup_not_in_spec`).

## Rocq → Lean map
* Namespace `Coneris.Examples.BloomFilter.BloomFilter` (for all four modules); `fp_error`,
  `fp_error_max`, `fp_error_bounded`, `fp_error_weaken`, `init_bloom_filter`,
  `insert_bloom_filter`, `lookup_bloom_filter`, `is_bloom_filter`, `is_bloom_filter_partial`,
  `bloom_filter_to_partial`, `bloom_filter_from_partial`: same names.
* The section variables `filter_size` and `num_hash` are explicit arguments (only of the
  declarations that use them). The context `HinG : inG Σ (gset_bijR nat nat)` is
  `[SetBijG GF ℕ ℕ pairset]` (as in `Coneris.Examples.Hash`); it is unused by the proofs, as in
  Rocq (where only `bloom_filter_init_spec` mentions it, in `Proof using`).
* `fp_error : nat → nat → R` is `ℝ≥0∞`-valued; `b / (filter_size + 1)` is
  `(b : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1)`, `pow x num_hash` is `x ^ num_hash`, and the real
  subtraction `filter_size + 1 - b` is the truncated `ℝ≥0∞` one. It is only evaluated in the
  branch `b < filter_size + 1` (the `else` branch of `bool_decide (b >= filter_size + 1)`),
  where it does not truncate. `fp_error_bounded` keeps the (trivial in `ℝ≥0∞`) lower bound
  `0 ≤ fp_error m b`.
* Programs are transcribed with the `cpl` notation. Rocq's string binder `"_"` (a *named*
  binder `BNamed "_"`, not `<>`) is kept as the string binder `"_"`.
  `let, ("hfuns", "arr") := e1 in e2` is `let (hfuns, arr) := e1; e2` (the same AST). Rocq's
  `init_hash filter_size`, `list_seq_fun`, `list_iter`, `array_init` are the antiquoted Lean
  values `&(init_hash filter_size)`, `&list_seq_fun`, `&list_iter`, `&array_init`.
* `gset nat` is `Finset ℕ`; `size idxs` is `idxs.card`; `gmap nat nat` is `hmap`
  (`Std.ExtTreeMap ℕ ℕ compare`, see `Coneris.Examples.Hash`), `dom m` is `hmap_dom m`,
  `m !!! e` is `m.getD e 0`; `arr !! i` (for `arr : list val`) is `arr[i]?`;
  `Forall P l` is `∀ x ∈ l, P x`; `length` is `List.length`.
* `[∗ list] k↦h;m ∈ hs;ms, hashfun filter_size h m` (index unused) is
  `[∗list] h;m ∈ hs;ms, hashfun filter_size h m`.
* `l ↦ (hfuns, LitV (LitLoc a))%V` is `l ↦ PairV hfuns (LitV (LitLoc a))`.

## Added
* `hmap_dom` (stdpp's `dom` on `gmap nat nat`) and `mem_hmap_dom`, `hmap_dom_insert`.
* `fp_error_zero`, `fp_error_succ` (the unfolding equations below `filter_size + 1`, Rocq:
  `simpl; case_bool_decide`), `div_le_one_aux`, `div_add_div_one_aux` (real arithmetic done
  inline in Rocq, e.g. `Rdiv_le_1`, `Rmult_inv_r`).
* Sanity checks (`example`) of the program ASTs.

## Omitted
* The commented-out Rocq class `bloom_filter` and the commented-out section
  `bloom_filter_par` (`parallel_test`, `parallel_test_spec`, an unfinished proof).
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

/-! ## `dom` for `hmap` -/

/-- Rocq (stdpp): `dom` on `gmap nat nat`. -/
def hmap_dom (m : hmap) : Finset ℕ := m.keys.toFinset

theorem mem_hmap_dom (m : hmap) (k : ℕ) : k ∈ hmap_dom m ↔ k ∈ m := by
  unfold hmap_dom
  rw [List.mem_toFinset, Std.ExtTreeMap.mem_keys]

/-- Rocq (stdpp): `dom_insert_L`. -/
theorem hmap_dom_insert (m : hmap) (k v : ℕ) :
    hmap_dom (m.insert k v) = {k} ∪ hmap_dom m := by
  ext x
  rw [mem_hmap_dom, Finset.mem_union, Finset.mem_singleton, mem_hmap_dom,
    Std.ExtTreeMap.mem_insert]
  simp only [Nat.compare_eq_eq, @eq_comm _ k x]

section bloom_filter

variable (filter_size num_hash : ℕ)

/-! ## False positive error -/

/-- Rocq: `fp_error`. Probability of false positive of one insertion after hashing `m`
elements into a Bloom filter containing `b` bits set to 1. -/
def fp_error (m b : ℕ) : ℝ≥0∞ :=
  if b ≥ filter_size + 1 then 1 else
    match m with
    | 0 => ((b : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1)) ^ num_hash
    | m' + 1 => ((b : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1)) * fp_error m' b +
        (((filter_size : ℝ≥0∞) + 1 - b) / ((filter_size : ℝ≥0∞) + 1)) * fp_error m' (b + 1)

theorem fp_error_zero (b : ℕ) (Hb : ¬ b ≥ filter_size + 1) :
    fp_error filter_size num_hash 0 b =
      ((b : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1)) ^ num_hash := by
  rw [fp_error, ite_eq_right_of_eq_false _ _ (eq_false Hb)]

theorem fp_error_succ (m b : ℕ) (Hb : ¬ b ≥ filter_size + 1) :
    fp_error filter_size num_hash (m + 1) b =
      ((b : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1)) * fp_error filter_size num_hash m b +
        (((filter_size : ℝ≥0∞) + 1 - b) / ((filter_size : ℝ≥0∞) + 1)) *
          fp_error filter_size num_hash m (b + 1) := by
  rw [fp_error, ite_eq_right_of_eq_false _ _ (eq_false Hb)]

/-- Rocq: `fp_error_max`. -/
theorem fp_error_max (m b : ℕ) (Hb : filter_size + 1 ≤ b) :
    fp_error filter_size num_hash m b = 1 := by
  cases m <;> simp [fp_error, Hb]

/-- `b / (filter_size + 1) ≤ 1` for `b ≤ filter_size + 1`. -/
theorem div_le_one_aux (b : ℕ) (Hb : b ≤ filter_size + 1) :
    (b : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1) ≤ 1 := by
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  exact_mod_cast Hb

/-- `b / (filter_size + 1) + (filter_size + 1 - b) / (filter_size + 1) = 1` for
`b ≤ filter_size + 1` (the subtraction does not truncate). -/
theorem div_add_div_one_aux (b : ℕ) (Hb : b ≤ filter_size + 1) :
    (b : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1) +
      ((filter_size : ℝ≥0∞) + 1 - b) / ((filter_size : ℝ≥0∞) + 1) = 1 := by
  rw [ENNReal.div_add_div_same, add_tsub_cancel_of_le (by exact_mod_cast Hb)]
  exact ENNReal.div_self (by simp) (by simp)

/-- Rocq: `fp_error_bounded`. -/
theorem fp_error_bounded (m b : ℕ) :
    0 ≤ fp_error filter_size num_hash m b ∧ fp_error filter_size num_hash m b ≤ 1 := by
  refine ⟨by simp, ?_⟩
  induction m generalizing b with
  | zero =>
    by_cases H : b ≥ filter_size + 1
    · rw [fp_error_max _ _ _ _ H]
    · rw [fp_error_zero _ _ _ H]
      exact pow_le_one₀ (by simp) (div_le_one_aux _ _ (by omega))
  | succ m IHm =>
    by_cases H : b ≥ filter_size + 1
    · rw [fp_error_max _ _ _ _ H]
    · rw [fp_error_succ _ _ _ _ H]
      calc _ ≤ (b : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1) * 1 +
            ((filter_size : ℝ≥0∞) + 1 - b) / ((filter_size : ℝ≥0∞) + 1) * 1 := by
            gcongr
            · exact IHm b
            · exact IHm (b + 1)
        _ = 1 := by rw [mul_one, mul_one, div_add_div_one_aux _ _ (by omega)]

/-- Rocq: `fp_error_weaken`. -/
theorem fp_error_weaken (m b : ℕ) :
    fp_error filter_size num_hash 0 b ≤ fp_error filter_size num_hash m b := by
  induction m generalizing b with
  | zero => exact le_rfl
  | succ m IHm =>
    have H2 := IHm (b + 1)
    have H3 : fp_error filter_size num_hash 0 b ≤ fp_error filter_size num_hash 0 (b + 1) := by
      by_cases H4 : b ≥ filter_size + 1
      · rw [fp_error_max _ _ 0 b H4, fp_error_max _ _ 0 (b + 1) (by omega)]
      by_cases H5 : b + 1 ≥ filter_size + 1
      · rw [fp_error_max _ _ 0 (b + 1) H5]
        exact (fp_error_bounded _ _ _ _).2
      rw [fp_error_zero _ _ _ H4, fp_error_zero _ _ _ H5]
      gcongr
      exact_mod_cast Nat.le_succ b
    by_cases H : b ≥ filter_size + 1
    · rw [fp_error_max _ _ (m + 1) b H]
      exact (fp_error_bounded _ _ _ _).2
    rw [fp_error_succ _ _ _ _ H]
    calc fp_error filter_size num_hash 0 b
        = (b : ℝ≥0∞) / ((filter_size : ℝ≥0∞) + 1) * fp_error filter_size num_hash 0 b +
            ((filter_size : ℝ≥0∞) + 1 - b) / ((filter_size : ℝ≥0∞) + 1) *
              fp_error filter_size num_hash 0 b := by
          rw [← add_mul, div_add_div_one_aux _ _ (by omega), one_mul]
      _ ≤ _ := by
          gcongr
          · exact IHm b
          · exact H3.trans H2

/-! ## Programs -/

/-- Rocq: `init_bloom_filter`. -/
def init_bloom_filter : expr :=
  cpl(λ "_",
    let hfuns := &list_seq_fun #(0 : ℕ) #num_hash (λ "_", &(init_hash filter_size) #()) in
    let arr := &array_init #(filter_size + 1 : ℕ) (λ x, #false) in
    let l := ref((hfuns, arr)) in
    l)

/-- Rocq: `insert_bloom_filter`. -/
def insert_bloom_filter : expr :=
  cpl(λ l v,
    let (hfuns, arr) := !l;
    &list_iter (λ h,
        let i := h v in
        arr +ₗ i ← #true) hfuns)

/-- Rocq: `lookup_bloom_filter`. -/
def lookup_bloom_filter : expr :=
  cpl(λ l v,
    let (hfuns, arr) := !l;
    let res := ref(#true) in
    &list_iter (λ h,
        let i := h v in
        if !(arr +ₗ i) then #() else res ← #false) hfuns;
    !res)

/-- Sanity check: the transcription of `insert_bloom_filter` is the intended AST
(Rocq's `let,` is `(λ: "arr", (λ: "hfuns", (λ: "arr", e) (Snd "arr")) (Fst "arr")) e1`). -/
example : insert_bloom_filter =
    expr.Rec .BAnon (.BNamed "l") (expr.Rec .BAnon (.BNamed "v")
      (App (expr.Rec .BAnon (.BNamed "arr")
        (App (expr.Rec .BAnon (.BNamed "hfuns")
          (App (expr.Rec .BAnon (.BNamed "arr")
            (App (App (Val list_iter)
              (expr.Rec .BAnon (.BNamed "h")
                (App (expr.Rec .BAnon (.BNamed "i")
                  (Store (BinOp .OffsetOp (Var "arr") (Var "i")) (Val (LitV (LitBool true)))))
                  (App (Var "h") (Var "v")))))
              (Var "hfuns")))
            (Snd (Var "arr"))))
          (Fst (Var "arr"))))
        (Load (Var "l")))) :=
  rfl

/-- Sanity check: the transcription of `init_bloom_filter`. -/
example : init_bloom_filter filter_size num_hash =
    expr.Rec .BAnon (.BNamed "_")
      (App (expr.Rec .BAnon (.BNamed "hfuns")
        (App (expr.Rec .BAnon (.BNamed "arr")
          (App (expr.Rec .BAnon (.BNamed "l") (Var "l"))
            (Alloc (Pair (Var "hfuns") (Var "arr")))))
          (App (App (Val array_init) (Val (LitV (LitInt ((filter_size + 1 : ℕ) : ℤ)))))
            (expr.Rec .BAnon (.BNamed "x") (Val (LitV (LitBool false)))))))
        (App (App (App (Val list_seq_fun) (Val (LitV (LitInt ((0 : ℕ) : ℤ)))))
            (Val (LitV (LitInt (num_hash : ℤ)))))
          (expr.Rec .BAnon (.BNamed "_")
            (App (Val (init_hash filter_size)) (Val (LitV LitUnit)))))) :=
  rfl

/-! ## Representation predicates -/

variable {GF : BundledGFunctors} [conerisGS GF] [HinG : SetBijG GF ℕ ℕ pairset]

/-- Rocq: `is_bloom_filter`. -/
def is_bloom_filter (l : Loc) (els : Finset ℕ) (rem : ℕ) : IProp GF :=
  iprop(∃ (hfuns : val) (hs : List val) (ms : List hmap) (a : Loc) (arr : List val)
      (idxs : Finset ℕ),
    ↯ (fp_error filter_size num_hash (num_hash * rem) idxs.card) ∗
    l ↦ PairV hfuns (LitV (LitLoc a)) ∗
      ⌜is_list_HO hs hfuns⌝ ∗
      ⌜hs.length = num_hash⌝ ∗
      ([∗list] h;m ∈ hs;ms, hashfun filter_size h m) ∗
      ⌜arr.length = filter_size + 1⌝ ∗
      ⌜idxs.card ≤ filter_size + 1⌝ ∗
      (a ↦∗ arr) ∗
      ⌜∀ m ∈ ms, els = hmap_dom m⌝ ∗
      ⌜∀ e, e ∈ els → ∀ m ∈ ms, m.getD e 0 ∈ idxs⌝ ∗
      ⌜∀ i, i ∈ idxs → arr[i]? = some (LitV (LitBool true))⌝ ∗
      ⌜∀ i, i ∈ idxs → i < filter_size + 1⌝ ∗
      ⌜∀ i, i < filter_size + 1 → i ∉ idxs → arr[i]? = some (LitV (LitBool false))⌝)

/-- Rocq: `is_bloom_filter_partial`. -/
def is_bloom_filter_partial (l : Loc) (e_new : ℕ) (els : Finset ℕ) (rem : ℕ)
    (hs_new hs_old : List val) (a : Loc) : IProp GF :=
  iprop(∃ (hfuns : val) (ms_new ms_old : List hmap) (arr : List val) (idxs : Finset ℕ),
    ↯ (fp_error filter_size num_hash (num_hash * rem + hs_old.length) idxs.card) ∗
    l ↦ PairV hfuns (LitV (LitLoc a)) ∗
      ⌜is_list_HO (hs_new ++ hs_old) hfuns⌝ ∗
      ⌜(hs_new ++ hs_old).length = num_hash⌝ ∗
      ([∗list] h;m ∈ hs_new;ms_new, hashfun filter_size h m) ∗
      ([∗list] h;m ∈ hs_old;ms_old, hashfun filter_size h m) ∗
      ⌜arr.length = filter_size + 1⌝ ∗
      ⌜idxs.card ≤ filter_size + 1⌝ ∗
      (a ↦∗ arr) ∗
      ⌜∀ m ∈ ms_old, els = hmap_dom m⌝ ∗
      ⌜∀ m ∈ ms_new, ({e_new} ∪ els) = hmap_dom m⌝ ∗
      ⌜∀ e, e ∈ els → ∀ m ∈ ms_old, m.getD e 0 ∈ idxs⌝ ∗
      ⌜∀ e, e ∈ ({e_new} ∪ els) → ∀ m ∈ ms_new, m.getD e 0 ∈ idxs⌝ ∗
      ⌜∀ i, i ∈ idxs → arr[i]? = some (LitV (LitBool true))⌝ ∗
      ⌜∀ i, i ∈ idxs → i < filter_size + 1⌝ ∗
      ⌜∀ i, i < filter_size + 1 → i ∉ idxs → arr[i]? = some (LitV (LitBool false))⌝)

/-- Rocq: `bloom_filter_to_partial`. -/
theorem bloom_filter_to_partial (l : Loc) (e_new : ℕ) (els : Finset ℕ) (rem : ℕ) :
    is_bloom_filter filter_size num_hash l els (rem + 1) ⊢@{IProp GF}
      ∃ hs a, is_bloom_filter_partial filter_size num_hash l e_new els rem [] hs a := by
  unfold is_bloom_filter
  iintro ⟨%hfuns, %hs, %ms, %a, %arr, %idxs, Herr, Hl, %Hhfuns, %Hlenhs, Hhs, %HlenA,
    %HsizeIdxs, Ha, %Hms, %Hidxs, %Htrue, %Hbd, %Hfalse⟩
  rw [show num_hash * (rem + 1) = num_hash * rem + num_hash by ring]
  iexists hs, a
  unfold is_bloom_filter_partial
  iexists hfuns, [], ms, arr, idxs
  rw [Hlenhs]
  simp only [List.nil_append]
  iframe
  isplitr
  · ipureintro; exact Hhfuns
  isplitr
  · ipureintro; exact Hlenhs
  isplitr
  · iempintro
  ipureintro
  exact ⟨HlenA, HsizeIdxs, Hms, by simp, Hidxs, by simp, Htrue, Hbd, Hfalse⟩

/-- Rocq: `bloom_filter_from_partial`. -/
theorem bloom_filter_from_partial (l : Loc) (e_new : ℕ) (els : Finset ℕ) (hs : List val)
    (a : Loc) (rem : ℕ) :
    is_bloom_filter_partial filter_size num_hash l e_new els rem hs [] a ⊢@{IProp GF}
      is_bloom_filter filter_size num_hash l ({e_new} ∪ els) rem := by
  unfold is_bloom_filter_partial
  iintro ⟨%hfuns, %ms_new, %ms_old, %arr, %idxs, Herr, Hl, %Hhfuns, %Hlenhs, Hhs_new, -,
    %HlenA, %HsizeIdxs, Ha, %Hms_old, %Hms_new, %Hidxs_old, %Hidxs_new, %Htrue, %Hbd, %Hfalse⟩
  simp only [List.length_nil, Nat.add_zero, List.append_nil] at Hhfuns Hlenhs ⊢
  unfold is_bloom_filter
  iexists hfuns, hs, ms_new, a, arr, idxs
  iframe
  ipureintro
  exact ⟨Hhfuns, Hlenhs, HlenA, HsizeIdxs, Hms_new, Hidxs_new, Htrue, Hbd, Hfalse⟩

end bloom_filter

end Coneris.Examples.BloomFilter.BloomFilter
