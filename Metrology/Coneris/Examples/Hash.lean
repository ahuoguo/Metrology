module

public import Metrology.Coneris.Lib.Map
public import Metrology.Coneris.ErrorRules
public import Iris.Instances.Lib.SetBij
public import Iris.Std.GenSetsInstances

/-!
# A simple sequential hash

Ported from clutch/theories/coneris/examples/hash.v

This example shows how to verify a simple sequential hash. This spec can then be used to prove
an amortized version.

## Rocq → Lean map
* Namespace `Coneris.Examples.Hash`; all definitions and lemmas keep their Rocq names:
  `init_hash_state`, `compute_hash_specialized`, `compute_hash`, `init_hash`, `coll_free`,
  `hash_view_auth`, `hash_view_frag`, `hash_view_auth_coll_free`,
  `hash_view_auth_duplicate_frag`, `hash_view_auth_frag_agree`, `hash_view_auth_insert`,
  `hashfun`, `coll_free_hashfun`, `coll_free_hashfun_implies_hashfun`, `timeless_hashfun`,
  `timeless_hashfun_amortized`, `coll_free_hashfun_implies_coll_free`,
  `hashfun_implies_bounded_range`, `coll_free_hashfun_implies_bounded_range`,
  `wp_init_hash_basic`, `wp_init_hash`, `coll_free_insert`, `wp_hashfun_prev`,
  `wp_coll_free_hashfun_prev`, `wp_coll_free_hashfun_frag_prev`, `wp_insert_no_coll`,
  `wp_insert_basic`, `wp_insert_avoid_set_adv` (section `simple_bit_hash`);
  `amortized_hashG` (fields `amortized_hash_credit`, `amortized_hash_gset_bij`),
  `amortized_error`, `hashfun_amortized`, `coll_free_hashfun_amortized`,
  `timeless_coll_free_hashfun_amortized`, `coll_free_hashfun_amortized_implies_coll_free`,
  `hashfun_amortized_implies_bounded_range`,
  `coll_free_hashfun_amortized_implies_bounded_range`, `wp_init_hash_amortized`,
  `hashfun_amortized_hashfun`, `wp_hashfun_prev_amortized`,
  `wp_coll_free_hashfun_prev_amortized`, `wp_coll_free_hashfun_prev_frag_amortized`,
  `amortized_inequality`, `hashfun_amortized_token_ineq`, `wp_insert_new_amortized`,
  `wp_insert_amortized` (section `amortized_hash`).
* The section variables `val_size` and `max_hash_size` are explicit arguments; the section
  hypothesis `max_hash_size_pos` is an explicit argument of `amortized_error` (as in Rocq, where
  the `Program Definition` uses it) and of the lemmas mentioning `amortized_error`.
* Programs are transcribed with the `cpl` notation (see `Metrology.ConProbLang.Notation`);
  `rand #val_size` is `rand(#val_size)`. The Lean term `hm` of `compute_hash_specialized` is
  antiquoted (`&hm`).
* `gmap nat nat` is `hmap := Std.ExtTreeMap ℕ ℕ compare` (as `gmap nat val` is `natmap` in
  `Coneris.Lib.Map`); `m !! k` is `m[k]?`, `m !!! k` (lookup with default `inhabitant = 0`) is
  `m.getD k 0`, `is_Some` is `Option.isSome`, `<[n := v]> m` is `m.insert n v`, `size m` is
  `m.size`, `map_to_list m` is `m.toList`, `(λ b, #b) <$> m` is `m.map (fun _ b => #b)`,
  `map_Forall P m` is `∀ k x, m[k]? = some x → P k x`, `m ⊆ m'` is
  `∀ k x, m[k]? = some x → m'[k]? = some x`.
* `gset_bijR nat nat` over `gset (nat * nat)` is iris-lean's `SetBij pairset` with
  `pairset := Std.ExtTreeSet (ℕ × ℕ) compare` (the order on pairs is the lexicographic order,
  the scoped instance `instOrdNatPair`); `inG Σ (gset_bijR nat nat)` is
  `[SetBijG GF ℕ ℕ pairset]`; `own γ (gset_bij_auth (DfracOwn 1) L)` is `γ ↪●BIJ L`,
  `own γ (gset_bij_elem k v)` is `γ ↪◯BIJ⟨k, v⟩`; `map_to_set pair m` is `map_to_set m`.
* `inG Σ (authR natR)` is `ElemG GF (constOF (Auth ℕ))` (iris-lean's constant-core CMRA on
  `(ℕ, +)`); `own γ (● n)` / `own γ (◯ n)` are `iOwn γ (● n)` / `iOwn γ (◯ n)`.
* Errors are `ℝ≥0∞`: `nnreal_div (nnreal_nat a) (nnreal_nat b)` is `(a : ℝ≥0∞) / (b : ℝ≥0∞)`.
  In `wp_insert_avoid_set_adv`, `ε εI εO : nonnegreal` are `ℝ≥0∞`, `size xs` (for
  `xs : gset nat`) is `xs.card` (`xs : Finset ℕ`), and the real subtraction
  `val_size + 1 - size xs` is the truncated `ℝ≥0∞` one; it does not truncate since every element
  of `xs` is `< val_size + 1`. In `hashfun_amortized`, `ε : nonnegreal` is `ε : ℝ≥0∞` and
  `sum_n_m (λ x, INR x) 0 (k - 1)` is `∑ x ∈ Finset.range k, (x : ℝ≥0∞)` (equal also for
  `k = 0`, as `sum_n_m _ 0 0 = INR 0 = 0`); the subtraction
  `(max_hash_size - 1) * k / 2 - sum ...` is truncated in `ℝ≥0∞`, but it never truncates in
  a satisfiable `hashfun_amortized` (the token `own γ (● max_hash_size) ∗ own γ (◯ k)` forces
  `k ≤ max_hash_size`, see `amortized_eps_closed`); in Rocq, a negative real would make the
  existential over `ε : nonnegreal` unsatisfiable. `amortized_inequality` (nonnegativity) is
  trivial in `ℝ≥0∞`; its real content (no truncation) is `amortized_eps_closed`.
* Texan triples `{{{ P }}} e @ E {{{ x, RET v; Q }}}` are iris-lean's
  `{{ P }} e @ E {{ x, RET v; Q }}`; `RET #n` for `n : nat` is `RET LitV (LitInt (n : ℤ))`.
* `x ∈ xs` for the sampled `x : fin (S val_size)` is `(x : ℕ) ∈ xs`.

## Added
* `hmap`, `pairset`, `instOrdNatPair`, `map_to_set`, `elem_of_map_to_set_pair` (stdpp's
  `elem_of_map_to_set_pair`), `map_to_set_empty`, `map_to_set_insert` (stdpp's
  `map_to_set_insert_L`), `map_insert_val` (stdpp's `fmap_insert` for the value map of
  `hashfun`): the stdpp map/set infrastructure.
* `hash_view_frag_persistent`, `hash_view_frag_timeless`, `hash_view_auth_timeless` (Rocq infers
  them).
* `own_frag_add` (Rocq: `own_op` with `auth_frag_op`/`nat_op`, used implicitly by
  `iDestruct`/`iCombine`).
* `amortized_eps` (the error of `hashfun_amortized` for `k` hashed keys, definitionally the
  inline Rocq expression), `nat_aux`, `nat_aux2`, `amortized_eps_closed`,
  `amortized_error_closed`, `amortized_step`: the real arithmetic of `wp_insert_new_amortized`
  (Rocq does it inline with `lra`).
* A sanity check (`example`) that `compute_hash_specialized` is the intended AST.

## Omitted
None (the Rocq file has no commented-out code apart from one commented variable
`Hineq`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Map

namespace Coneris.Examples.Hash

/-! ## Maps and sets of pairs -/

/-- The lexicographic order on pairs (used for `pairset`). -/
scoped instance instOrdNatPair : Ord (ℕ × ℕ) := lexOrd

/-- Rocq: `gmap nat nat`. -/
abbrev hmap : Type := Std.ExtTreeMap ℕ ℕ compare

/-- Rocq: `gset (nat * nat)`. -/
abbrev pairset : Type := Std.ExtTreeSet (ℕ × ℕ) compare

/-- Rocq (stdpp): `map_to_set pair`. -/
def map_to_set (m : hmap) : pairset := Std.ExtTreeSet.ofList m.toList compare

/-- Rocq (stdpp): `elem_of_map_to_set_pair`. -/
theorem elem_of_map_to_set_pair (m : hmap) (k v : ℕ) :
    (k, v) ∈ map_to_set m ↔ m[k]? = some v := by
  unfold map_to_set
  rw [Std.ExtTreeSet.mem_ofList, List.contains_iff_mem,
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]

/-- Rocq (stdpp): `map_to_set_empty`. -/
theorem map_to_set_empty : map_to_set (∅ : hmap) = (∅ : pairset) := by
  apply LawfulSet.ext
  rintro ⟨k, v⟩
  rw [elem_of_map_to_set_pair]
  simp only [Std.ExtTreeMap.getElem?_empty, reduceCtorEq, false_iff]
  exact LawfulSet.mem_empty

/-- Rocq (stdpp): `map_to_set_insert_L`. -/
theorem map_to_set_insert (m : hmap) (n x : ℕ) (h : m[n]? = none) :
    map_to_set (m.insert n x) = ({(n, x)} ∪ map_to_set m : pairset) := by
  apply LawfulSet.ext
  rintro ⟨k, v⟩
  rw [LawfulSet.mem_union, LawfulSet.mem_singleton, elem_of_map_to_set_pair,
    elem_of_map_to_set_pair, Std.ExtTreeMap.getElem?_insert]
  by_cases hk : n = k
  · subst hk; simp_all [eq_comm]
  · have : compare n k ≠ .eq := by simpa using hk
    simp [this, Ne.symm hk]

/-- Rocq (stdpp): `fmap_insert`, for the value map of `hashfun`. -/
theorem map_insert_val (m : hmap) (n x : ℕ) :
    (m.insert n x).map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ))) =
      (m.map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ)))).insert n (LitV (LitInt (x : ℤ))) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_map]
  split <;> simp

section simple_bit_hash

variable {GF : BundledGFunctors} [conerisGS GF] [HinG : SetBijG GF ℕ ℕ pairset]
variable (val_size : ℕ)

/-! ## Programs -/

/-- Rocq: `init_hash_state`. A hash function's internal state is a map from previously queried
keys to their hash value. -/
def init_hash_state : val := init_map

/-- Rocq: `compute_hash_specialized`. To hash a value `v`, we check whether it is in the map
(i.e. it has been previously hashed). If it has we return the saved hash value, otherwise we
draw a hash value and save it in the map. -/
def compute_hash_specialized (hm : val) : val :=
  cpl_val(λ v,
    match &get &hm v with
    | some(b) => b
    | none() =>
        let b := rand(#val_size) in
        &set &hm v b;
        b)

/-- Rocq: `compute_hash`. -/
def compute_hash : val :=
  cpl_val(λ hm v,
    match &get hm v with
    | some(b) => b
    | none() =>
        let b := rand(#val_size) in
        &set hm v b;
        b)

/-- Rocq: `init_hash`. `init_hash` returns a hash as a function, basically wrapping the
internal state in the returned function. -/
def init_hash : val :=
  cpl_val(λ <>,
    let hm := &init_hash_state #() in
    &(compute_hash val_size) hm)

/-- Sanity check: the transcription of `compute_hash_specialized` is the intended AST. -/
example (hm : val) : compute_hash_specialized val_size hm =
    val.RecV .BAnon (.BNamed "v")
      (Match (App (App (Val get) (Val hm)) (Var "v"))
        .BAnon (Let (.BNamed "b") (Rand (Val (LitV (LitInt (val_size : ℤ)))) (Val (LitV LitUnit)))
          (Seq (App (App (App (Val set) (Val hm)) (Var "v")) (Var "b")) (Var "b")))
        (.BNamed "b") (Var "b")) :=
  rfl

/-! ## Collision freedom and the ghost bijection -/

/-- Rocq: `coll_free`. A hash function is collision free if the partial map it implements is
an injective function. -/
def coll_free (m : hmap) : Prop :=
  ∀ k1 k2, (m[k1]?).isSome → (m[k2]?).isSome → m.getD k1 0 = m.getD k2 0 → k1 = k2

/-- Rocq: `hash_view_auth`. -/
def hash_view_auth (m : hmap) (γ : GName) : IProp GF := γ ↪●BIJ (map_to_set m)

/-- Rocq: `hash_view_frag`. -/
def hash_view_frag (k v : ℕ) (γ : GName) : IProp GF := γ ↪◯BIJ⟨k, v⟩

instance hash_view_frag_persistent (k v : ℕ) (γ : GName) :
    Persistent (hash_view_frag (GF := GF) k v γ) := by
  unfold hash_view_frag; infer_instance

instance hash_view_frag_timeless (k v : ℕ) (γ : GName) :
    Timeless (hash_view_frag (GF := GF) k v γ) := by
  unfold hash_view_frag; infer_instance

instance hash_view_auth_timeless (m : hmap) (γ : GName) :
    Timeless (hash_view_auth (GF := GF) m γ) := by
  unfold hash_view_auth; infer_instance

omit [conerisGS GF] in
/-- Rocq: `hash_view_auth_coll_free`. -/
theorem hash_view_auth_coll_free (m : hmap) (γ2 : GName) :
    hash_view_auth m γ2 ⊢@{IProp GF} ⌜coll_free m⌝ := by
  unfold hash_view_auth
  refine set_bij_own_valid.trans (pure_mono ?_)
  rintro ⟨-, H⟩ k1 k2 H1 H2 H3
  obtain ⟨v1, K1⟩ := Option.isSome_iff_exists.mp H1
  obtain ⟨v2, K2⟩ := Option.isSome_iff_exists.mp H2
  have hv : v1 = v2 := by
    rw [Std.ExtTreeMap.getD_eq_getD_getElem?, Std.ExtTreeMap.getD_eq_getD_getElem?, K1, K2] at H3
    exact H3
  subst hv
  exact ((H ((elem_of_map_to_set_pair m k1 v1).mpr K1)).2 k2
    ((elem_of_map_to_set_pair m k2 v1).mpr K2)).symm

omit [conerisGS GF] in
/-- Rocq: `hash_view_auth_duplicate_frag`. -/
theorem hash_view_auth_duplicate_frag (m : hmap) (n b : ℕ) (γ2 : GName) (Hsome : m[n]? = some b) :
    hash_view_auth m γ2 ⊢@{IProp GF} |==> (hash_view_auth m γ2 ∗ hash_view_frag n b γ2) := by
  unfold hash_view_auth hash_view_frag
  refine .trans ?_ BIUpdate.intro
  exact persistent_entails_left
    (set_bij_own_elem_get _ _ ((elem_of_map_to_set_pair m n b).mpr Hsome))

omit [conerisGS GF] in
/-- Rocq: `hash_view_auth_frag_agree`. -/
theorem hash_view_auth_frag_agree (m : hmap) (γ2 : GName) (k v : ℕ) :
    hash_view_auth m γ2 ∗ hash_view_frag k v γ2 ⊢@{IProp GF} ⌜m[k]? = some v⌝ := by
  unfold hash_view_auth hash_view_frag
  exact (set_bij_elem_of k v).trans (pure_mono (elem_of_map_to_set_pair m k v).mp)

omit [conerisGS GF] in
/-- Rocq: `hash_view_auth_insert`. -/
theorem hash_view_auth_insert (m : hmap) (n x : ℕ) (γ : GName) (H1 : m[n]? = none)
    (H2 : ∀ y ∈ m.toList.map (fun p => p.2), x ≠ y) :
    hash_view_auth m γ ⊢@{IProp GF}
      |==> (hash_view_auth (m.insert n x) γ ∗ hash_view_frag n x γ) := by
  unfold hash_view_auth hash_view_frag
  rw [map_to_set_insert m n x H1]
  iintro H
  iapply set_bij_own_extend n x ?_ ?_ $$ H
  · intro b' hb
    rw [elem_of_map_to_set_pair, H1] at hb
    cases hb
  · intro a' ha
    rw [elem_of_map_to_set_pair] at ha
    apply H2 x _ rfl
    exact List.mem_map.mpr ⟨(a', x), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr ha, rfl⟩

/-! ## The hash function -/

/-- Rocq: `hashfun`. -/
def hashfun (f : val) (m : hmap) : IProp GF :=
  iprop(∃ hm : Loc, ⌜f = compute_hash_specialized val_size (LitV (LitLoc hm))⌝ ∗
    map_list hm (m.map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ)))) ∗
    ⌜∀ ind i : ℕ, m[ind]? = some i → 0 ≤ i ∧ i ≤ val_size⌝)

/-- Rocq: `coll_free_hashfun`. -/
def coll_free_hashfun (f : val) (m : hmap) (γ : GName) : IProp GF :=
  iprop(hashfun val_size f m ∗ hash_view_auth m γ)

/-- Rocq: `coll_free_hashfun_implies_hashfun`. -/
theorem coll_free_hashfun_implies_hashfun (f : val) (m : hmap) (γ : GName) :
    coll_free_hashfun val_size f m γ ⊢@{IProp GF} hashfun val_size f m := by
  unfold coll_free_hashfun
  iintro ⟨H, -⟩
  iexact H

/-- Rocq: `timeless_hashfun`. -/
instance timeless_hashfun (f : val) (m : hmap) : Timeless (hashfun (GF := GF) val_size f m) := by
  unfold hashfun; infer_instance

/-- Rocq: `timeless_hashfun_amortized`. -/
instance timeless_hashfun_amortized (f : val) (m : hmap) (γ : GName) :
    Timeless (coll_free_hashfun (GF := GF) val_size f m γ) := by
  unfold coll_free_hashfun; infer_instance

/-- Rocq: `coll_free_hashfun_implies_coll_free`. -/
theorem coll_free_hashfun_implies_coll_free (f : val) (m : hmap) (γ : GName) :
    coll_free_hashfun val_size f m γ ⊢@{IProp GF} ⌜coll_free m⌝ := by
  unfold coll_free_hashfun
  iintro ⟨-, H⟩
  iapply hash_view_auth_coll_free $$ H

omit HinG in
/-- Rocq: `hashfun_implies_bounded_range`. -/
theorem hashfun_implies_bounded_range (f : val) (m : hmap) (idx x : ℕ) :
    ⊢@{IProp GF} hashfun val_size f m -∗ ⌜m[idx]? = some x⌝ -∗ ⌜0 ≤ x ∧ x ≤ val_size⌝ := by
  unfold hashfun
  iintro ⟨%hm, %_, _H, %K⟩ %Hx
  ipureintro
  exact K idx x Hx

/-- Rocq: `coll_free_hashfun_implies_bounded_range`. -/
theorem coll_free_hashfun_implies_bounded_range (f : val) (m : hmap) (idx x : ℕ) (γ : GName) :
    ⊢@{IProp GF} coll_free_hashfun val_size f m γ -∗ ⌜m[idx]? = some x⌝ -∗
      ⌜0 ≤ x ∧ x ≤ val_size⌝ := by
  unfold coll_free_hashfun
  iintro ⟨H, -⟩ %Hx
  iapply hashfun_implies_bounded_range val_size f m idx x $$ H
  ipureintro
  exact Hx

/-- Rocq: `wp_init_hash_basic`. -/
theorem wp_init_hash_basic (E : CoPset) :
    {{ True }} cpl(&(init_hash val_size) #()) @ E
    {{ f, RET f; (hashfun val_size f ∅ : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold init_hash
  wp_pures
  unfold init_hash_state
  wp_apply wp_init_map $$ [] with %l Hm
  · itrivial
  unfold compute_hash
  wp_pures
  iapply HΦ
  unfold hashfun
  imodintro
  iexists l
  isplitr
  · ipureintro; rfl
  isplitl
  · rw [Std.ExtTreeMap.map_eq_empty_iff.mpr rfl]
    iexact Hm
  ipureintro
  simp

/-- Rocq: `wp_init_hash`. -/
theorem wp_init_hash (E : CoPset) :
    {{ True }} cpl(&(init_hash val_size) #()) @ E
    {{ f, RET f; (∃ γ, |={E}=> coll_free_hashfun val_size f ∅ γ : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold init_hash
  wp_pures
  unfold init_hash_state
  wp_apply wp_init_map $$ [] with %l Hm
  · itrivial
  unfold compute_hash
  wp_pures
  imod (set_bij_own_alloc_empty (GF := GF) (S := pairset)) with ⟨%γ2, Hview⟩
  iapply HΦ
  imodintro
  iexists γ2
  imodintro
  unfold coll_free_hashfun hashfun hash_view_auth
  rw [map_to_set_empty]
  isplitr [Hview]
  · iexists l
    isplitr
    · ipureintro; rfl
    isplitl
    · rw [Std.ExtTreeMap.map_eq_empty_iff.mpr rfl]
      iexact Hm
    ipureintro
    simp
  iexact Hview

/-- Rocq: `coll_free_insert`. -/
theorem coll_free_insert (m : hmap) (n z : ℕ) (_Hnone : m[n]? = none) (Hcoll : coll_free m)
    (HForall : ∀ x ∈ m.toList, z ≠ x.2) : coll_free (m.insert n z) := by
  intro k1 k2 Hk1 Hk2 Heq
  have hval : ∀ k v, m[k]? = some v → z ≠ v := fun k v h =>
    HForall (k, v) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr h)
  simp only [Std.ExtTreeMap.getD_eq_getD_getElem?, Std.ExtTreeMap.getElem?_insert] at Heq Hk1 Hk2
  by_cases h1 : n = k1 <;> by_cases h2 : n = k2
  · exact h1 ▸ h2
  · have c1 : compare n k1 = .eq := by simpa using h1
    have c2 : compare n k2 ≠ .eq := by simpa using h2
    simp only [c1, c2, ite_true, ite_false, Option.getD_some] at Heq Hk2
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp Hk2
    rw [hv, Option.getD_some] at Heq
    exact absurd Heq (hval k2 v hv)
  · have c1 : compare n k1 ≠ .eq := by simpa using h1
    have c2 : compare n k2 = .eq := by simpa using h2
    simp only [c1, c2, ite_true, ite_false, Option.getD_some] at Heq Hk1
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp Hk1
    rw [hv, Option.getD_some] at Heq
    exact absurd Heq.symm (hval k1 v hv)
  · have c1 : compare n k1 ≠ .eq := by simpa using h1
    have c2 : compare n k2 ≠ .eq := by simpa using h2
    simp only [c1, c2, ite_false] at Heq Hk1 Hk2
    apply Hcoll k1 k2 Hk1 Hk2
    simpa only [Std.ExtTreeMap.getD_eq_getD_getElem?] using Heq

/-- Rocq: `wp_hashfun_prev`. -/
theorem wp_hashfun_prev (E : CoPset) (f : val) (m : hmap) (n b : ℕ) (Hlookup : m[n]? = some b) :
    {{ hashfun val_size f m }} cpl(&f #n) @ E
    {{ RET LitV (LitInt (b : ℤ)); (hashfun val_size f m : IProp GF) }} := by
  iintro %Φ Hhash HΦ
  unfold hashfun
  icases Hhash with ⟨%hm, %Hf, H, %Hbound⟩
  subst Hf
  unfold compute_hash_specialized
  wp_pures
  wp_apply wp_get hm _ n $$ H with %vret ⟨Hhash, %Hv⟩
  subst Hv
  rw [Std.ExtTreeMap.getElem?_map, Hlookup]
  simp only [Option.map_some, opt_to_val]
  wp_pures
  iapply HΦ
  iexists hm
  iframe
  ipureintro
  exact ⟨rfl, Hbound⟩

/-- Rocq: `wp_coll_free_hashfun_prev`. -/
theorem wp_coll_free_hashfun_prev (E : CoPset) (f : val) (m : hmap) (γ : GName) (n b : ℕ)
    (Hlookup : m[n]? = some b) :
    {{ coll_free_hashfun val_size f m γ }} cpl(&f #n) @ E
    {{ RET LitV (LitInt (b : ℤ));
        (coll_free_hashfun val_size f m γ ∗ hash_view_frag n b γ : IProp GF) }} := by
  unfold coll_free_hashfun
  iintro %Φ ⟨Hhash, Hauth⟩ HΦ
  unfold hashfun
  icases Hhash with ⟨%hm, %Hf, H, %Hbound⟩
  subst Hf
  unfold compute_hash_specialized
  wp_pures
  wp_apply wp_get hm _ n $$ H with %vret ⟨Hhash, %Hv⟩
  subst Hv
  rw [Std.ExtTreeMap.getElem?_map, Hlookup]
  simp only [Option.map_some, opt_to_val]
  wp_pures
  imod hash_view_auth_duplicate_frag m n b γ Hlookup $$ Hauth with ⟨Hauth, Hfrag⟩
  imodintro
  iapply HΦ
  iframe
  ipureintro
  exact ⟨rfl, Hbound⟩

/-- Rocq: `wp_coll_free_hashfun_frag_prev`. -/
theorem wp_coll_free_hashfun_frag_prev (E : CoPset) (f : val) (m : hmap) (γ : GName)
    (n b : ℕ) :
    {{ coll_free_hashfun val_size f m γ ∗ hash_view_frag n b γ }} cpl(&f #n) @ E
    {{ RET LitV (LitInt (b : ℤ)); (coll_free_hashfun val_size f m γ : IProp GF) }} := by
  unfold coll_free_hashfun
  iintro %Φ ⟨⟨Hhash, Hauth⟩, #Hfrag⟩ HΦ
  ihave %Hlk := hash_view_auth_frag_agree m γ n b $$ [Hauth Hfrag]
  · isplitl [Hauth]
    · iexact Hauth
    · iexact Hfrag
  iapply wp_coll_free_hashfun_prev val_size E f m γ n b Hlk $$ [Hhash Hauth]
  · unfold coll_free_hashfun
    iframe
  iintro !> H
  unfold coll_free_hashfun
  icases H with ⟨⟨H1, H2⟩, -⟩
  iapply HΦ
  iframe

/-- Rocq: `wp_insert_no_coll`. -/
theorem wp_insert_no_coll (E : CoPset) (f : val) (m : hmap) (n : ℕ) (γ : GName)
    (Hlookup : m[n]? = none) :
    {{ coll_free_hashfun val_size f m γ ∗
        ↯ ((m.toList.length : ℝ≥0∞) / ((val_size + 1 : ℕ) : ℝ≥0∞)) }} cpl(&f #n) @ E
    {{ (v : ℕ), RET LitV (LitInt (v : ℤ));
        (coll_free_hashfun val_size f (m.insert n v) γ ∗ hash_view_frag n v γ : IProp GF) }} := by
  unfold coll_free_hashfun
  iintro %Φ ⟨⟨Hhash, Hauth⟩, Herr⟩ HΦ
  unfold hashfun
  icases Hhash with ⟨%hm, %Hf, H, %Hbound⟩
  subst Hf
  unfold compute_hash_specialized
  wp_pures
  wp_apply wp_get hm _ n $$ H with %vret ⟨Hhash, %Hv⟩
  subst Hv
  rw [Std.ExtTreeMap.getElem?_map, Hlookup]
  simp only [Option.map_none, opt_to_val]
  wp_pures
  wp_bind (Rand _ _)
  iapply wp_rand_err_list_nat val_size val_size (m.toList.map (fun p => p.2)) (by simp)
  isplitl [Herr]
  · rw [List.length_map, Nat.cast_add, Nat.cast_one]
    iexact Herr
  iintro %x %HForall
  wp_pures
  wp_apply wp_set hm _ n _ $$ Hhash with Hlist
  wp_pures
  imod hash_view_auth_insert m n x γ Hlookup (fun y hy => (HForall y hy)) $$ Hauth
    with ⟨Hauth, Hfrag⟩
  imodintro
  iapply HΦ
  iframe
  iexists hm
  rw [map_insert_val]
  iframe
  ipureintro
  refine ⟨rfl, ?_⟩
  intro ind i hi
  rw [Std.ExtTreeMap.getElem?_insert] at hi
  split at hi
  · cases hi; have := x.isLt; omega
  · exact Hbound ind i hi

/-- Rocq: `wp_insert_basic`. -/
theorem wp_insert_basic (E : CoPset) (f : val) (m : hmap) (n : ℕ) (Hlookup : m[n]? = none) :
    {{ hashfun val_size f m }} cpl(&f #n) @ E
    {{ (v : ℕ), RET LitV (LitInt (v : ℤ));
        (⌜v < val_size + 1⌝ ∗ hashfun val_size f (m.insert n v) : IProp GF) }} := by
  iintro %Φ Hhash HΦ
  unfold hashfun
  icases Hhash with ⟨%hm, %Hf, H, %Hbound⟩
  subst Hf
  unfold compute_hash_specialized
  wp_pures
  wp_apply wp_get hm _ n $$ H with %vret ⟨Hhash, %Hv⟩
  subst Hv
  rw [Std.ExtTreeMap.getElem?_map, Hlookup]
  simp only [Option.map_none, opt_to_val]
  wp_pures
  wp_bind (Rand _ _)
  wp_apply wp_rand val_size val_size (by simp) $$ [] with %x -
  · itrivial
  wp_pures
  wp_apply wp_set hm _ n _ $$ Hhash with Hlist
  wp_pures
  iapply HΦ
  isplitr
  · ipureintro
    exact x.isLt
  iexists hm
  rw [map_insert_val]
  iframe
  ipureintro
  refine ⟨rfl, ?_⟩
  intro ind i hi
  rw [Std.ExtTreeMap.getElem?_insert] at hi
  split at hi
  · cases hi; have := x.isLt; omega
  · exact Hbound ind i hi

/-- Rocq: `wp_insert_avoid_set_adv`. -/
theorem wp_insert_avoid_set_adv (E : CoPset) (f : val) (m : hmap) (n : ℕ) (xs : Finset ℕ)
    (ε εI εO : ℝ≥0∞) (Hlookup : m[n]? = none) (Hlt : ∀ x : ℕ, x ∈ xs → x < val_size + 1)
    (HεEq : ε = εI * xs.card / ((val_size : ℝ≥0∞) + 1) +
      εO * ((val_size : ℝ≥0∞) + 1 - xs.card) / ((val_size : ℝ≥0∞) + 1)) :
    {{ hashfun val_size f m ∗ ↯ ε }} cpl(&f #n) @ E
    {{ (v : ℕ), RET LitV (LitInt (v : ℤ));
        (⌜v < val_size + 1⌝ ∗ hashfun val_size f (m.insert n v) ∗
          ((⌜v ∉ xs⌝ ∗ ↯ εO) ∨ (⌜v ∈ xs⌝ ∗ ↯ εI)) : IProp GF) }} := by
  iintro %Φ ⟨Hhash, Herr⟩ HΦ
  unfold hashfun
  icases Hhash with ⟨%hm, %Hf, H, %Hbound⟩
  subst Hf
  unfold compute_hash_specialized
  wp_pures
  wp_apply wp_get hm _ n $$ H with %vret ⟨Hhash, %Hv⟩
  subst Hv
  rw [Std.ExtTreeMap.getElem?_map, Hlookup]
  simp only [Option.map_none, opt_to_val]
  wp_pures
  wp_bind (Rand _ _)
  have Hleq : εI * xs.card + εO * ((val_size : ℝ≥0∞) + 1 - xs.card) ≤
      ε * ((val_size : ℝ≥0∞) + 1) := by
    rw [HεEq, ENNReal.div_add_div_same, ENNReal.div_mul_cancel (by simp) (by simp)]
  iapply wp_rand_err_set_in_out val_size val_size xs ε εI εO (by simp) Hlt Hleq
  isplitl [Herr]
  · iexact Herr
  iintro %x HK
  wp_pures
  wp_apply wp_set hm _ n _ $$ Hhash with Hlist
  wp_pures
  iapply HΦ
  iframe
  isplitr
  · ipureintro
    exact x.isLt
  iexists hm
  rw [map_insert_val]
  iframe
  ipureintro
  refine ⟨rfl, ?_⟩
  intro ind i hi
  rw [Std.ExtTreeMap.getElem?_insert] at hi
  split at hi
  · cases hi; have := x.isLt; omega
  · exact Hbound ind i hi

end simple_bit_hash

/-- Arithmetic helper for `amortized_eps_closed`. -/
theorem nat_aux (k h : ℕ) (hk : k ≤ h) : (h - 1) * k - k * (k - 1) = k * (h - k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rcases k with _ | k
  · simp
  · have e1 : k + 1 + d - 1 = k + d := by omega
    have e2 : k + 1 + d - (k + 1) = d := by omega
    rw [e1, e2, Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring

/-- Arithmetic helper for `amortized_step`. -/
theorem nat_aux2 (k h : ℕ) (hk : k + 1 ≤ h) :
    (h - 1) + k * (h - k) = 2 * k + (k + 1) * (h - (k + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have e1 : k + 1 + d - 1 = k + d := by omega
  have e2 : k + 1 + d - k = d + 1 := by omega
  have e3 : k + 1 + d - (k + 1) = d := by omega
  rw [e1, e2, e3]
  ring

section amortized_hash

/-- Rocq: `amortized_hashG`. -/
class amortized_hashG (GF : BundledGFunctors) where
  amortized_hash_credit : ElemG GF (constOF (Auth ℕ))
  amortized_hash_gset_bij : SetBijG GF ℕ ℕ pairset

attribute [reducible, instance] amortized_hashG.amortized_hash_credit
  amortized_hashG.amortized_hash_gset_bij

variable {GF : BundledGFunctors} [conerisGS GF] [Hah : amortized_hashG GF]
variable (val_size : ℕ) (max_hash_size : ℕ)

set_option linter.unusedVariables false in
/-- Rocq: `amortized_error` (a `Program Definition` whose nonnegativity obligation uses
`max_hash_size_pos`). -/
def amortized_error (max_hash_size_pos : 0 < max_hash_size) : ℝ≥0∞ :=
  ((max_hash_size : ℝ≥0∞) - 1) / (2 * ((val_size : ℝ≥0∞) + 1))

/-- The error stored in `hashfun_amortized` for `k` hashed keys (Rocq: inline). -/
def amortized_eps (k : ℕ) : ℝ≥0∞ :=
  (((max_hash_size : ℝ≥0∞) - 1) * k / 2 - ∑ x ∈ Finset.range k, (x : ℝ≥0∞)) /
    ((val_size : ℝ≥0∞) + 1)

/-- Rocq: `hashfun_amortized`. -/
def hashfun_amortized (f : val) (m : hmap) (γ : GName) : IProp GF :=
  iprop(∃ (k : ℕ) (ε : ℝ≥0∞),
    hashfun val_size f m ∗
    ⌜k = m.size⌝ ∗
    ⌜ε = (((max_hash_size : ℝ≥0∞) - 1) * k / 2 - ∑ x ∈ Finset.range k, (x : ℝ≥0∞)) /
      ((val_size : ℝ≥0∞) + 1)⌝ ∗
    ↯ ε ∗
    iOwn (F := constOF (Auth ℕ)) γ (● max_hash_size) ∗
    iOwn (F := constOF (Auth ℕ)) γ (◯ k))

/-- Rocq: `coll_free_hashfun_amortized`. -/
def coll_free_hashfun_amortized (f : val) (m : hmap) (γ1 γ2 : GName) : IProp GF :=
  iprop(hashfun_amortized val_size max_hash_size f m γ1 ∗ hash_view_auth m γ2)

/-- Rocq: `timeless_coll_free_hashfun_amortized`. -/
instance timeless_coll_free_hashfun_amortized (f : val) (m : hmap) (γ : GName) :
    Timeless (hashfun_amortized (GF := GF) val_size max_hash_size f m γ) := by
  unfold hashfun_amortized
  have : ∀ k : ℕ, Timeless (iOwn (GF := GF) (F := constOF (Auth ℕ)) γ (◯ k)) :=
    fun _ => inferInstance
  have : Timeless (iOwn (GF := GF) (F := constOF (Auth ℕ)) γ (● max_hash_size)) := inferInstance
  infer_instance

/-- The closed form of `amortized_eps` for `k ≤ max_hash_size`: the truncated subtraction in
its definition does not truncate (Rocq: `amortized_inequality` and the `lra` computations). -/
theorem amortized_eps_closed (k : ℕ) (hk : k ≤ max_hash_size) :
    amortized_eps val_size max_hash_size k =
      ((k * (max_hash_size - k) : ℕ) : ℝ≥0∞) / (2 * ((val_size : ℝ≥0∞) + 1)) := by
  unfold amortized_eps
  have hs : (∑ x ∈ Finset.range k, (x : ℝ≥0∞)) = ((k * (k - 1) : ℕ) : ℝ≥0∞) / 2 := by
    rw [← Finset.sum_range_id_mul_two, Nat.cast_mul, ← Nat.cast_sum]
    push_cast
    rw [ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  have hm : ((max_hash_size : ℝ≥0∞) - 1) * k = (((max_hash_size - 1) * k : ℕ) : ℝ≥0∞) := by
    push_cast [ENNReal.natCast_sub]; rfl
  rw [hs, hm, ← ENNReal.sub_div (fun _ _ => by norm_num), ← ENNReal.natCast_sub,
    nat_aux k max_hash_size hk]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp),
    mul_assoc]

/-- The closed form of `amortized_error`. -/
theorem amortized_error_closed (max_hash_size_pos : 0 < max_hash_size) :
    amortized_error val_size max_hash_size max_hash_size_pos =
      ((max_hash_size - 1 : ℕ) : ℝ≥0∞) / (2 * ((val_size : ℝ≥0∞) + 1)) := by
  unfold amortized_error
  rw [ENNReal.natCast_sub, Nat.cast_one]

/-- The error bookkeeping of one fresh insertion (Rocq: the `ec_eq` computation in
`wp_insert_new_amortized`). -/
theorem amortized_step (max_hash_size_pos : 0 < max_hash_size) (k : ℕ)
    (hk : k + 1 ≤ max_hash_size) :
    amortized_error val_size max_hash_size max_hash_size_pos +
        amortized_eps val_size max_hash_size k =
      (k : ℝ≥0∞) / ((val_size + 1 : ℕ) : ℝ≥0∞) + amortized_eps val_size max_hash_size (k + 1) := by
  rw [amortized_error_closed, amortized_eps_closed _ _ _ (by omega),
    amortized_eps_closed _ _ _ hk, ENNReal.div_add_div_same, Nat.cast_add, Nat.cast_one,
    ← ENNReal.mul_div_mul_left (k : ℝ≥0∞) _ (two_ne_zero) (by simp), ENNReal.div_add_div_same]
  congr 1
  have := nat_aux2 k max_hash_size hk
  exact_mod_cast this

/-- Rocq: `own_op` with `auth_frag_op` and `nat_op` (splitting a token). -/
theorem own_frag_add (γ : GName) (a b : ℕ) :
    iOwn (GF := GF) (F := constOF (Auth ℕ)) γ (◯ (a + b)) ⊣⊢
      iOwn (F := constOF (Auth ℕ)) γ (◯ a) ∗ iOwn (F := constOF (Auth ℕ)) γ (◯ b) := by
  have : (◯ (a + b) : Auth ℕ) = (◯ a : Auth ℕ) • ◯ b := Auth.frag_op
  rw [this]
  exact iOwn_op

/-- Rocq: `coll_free_hashfun_amortized_implies_coll_free`. -/
theorem coll_free_hashfun_amortized_implies_coll_free (f : val) (m : hmap) (γ1 γ2 : GName) :
    coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2 ⊢@{IProp GF}
      ⌜coll_free m⌝ := by
  unfold coll_free_hashfun_amortized
  iintro ⟨-, H⟩
  iapply hash_view_auth_coll_free $$ H

/-- Rocq: `hashfun_amortized_implies_bounded_range`. -/
theorem hashfun_amortized_implies_bounded_range (f : val) (m : hmap) (γ : GName) (idx x : ℕ) :
    ⊢@{IProp GF} hashfun_amortized val_size max_hash_size f m γ -∗ ⌜m[idx]? = some x⌝ -∗
      ⌜0 ≤ x ∧ x ≤ val_size⌝ := by
  unfold hashfun_amortized
  iintro ⟨%k, %ε, H, -⟩ %Hx
  iapply hashfun_implies_bounded_range val_size f m idx x $$ H
  ipureintro
  exact Hx

/-- Rocq: `coll_free_hashfun_amortized_implies_bounded_range`. -/
theorem coll_free_hashfun_amortized_implies_bounded_range (f : val) (m : hmap)
    (γ1 γ2 : GName) (idx x : ℕ) :
    ⊢@{IProp GF} coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2 -∗
      ⌜m[idx]? = some x⌝ -∗ ⌜0 ≤ x ∧ x ≤ val_size⌝ := by
  unfold coll_free_hashfun_amortized
  iintro ⟨H, -⟩ %Hx
  iapply hashfun_amortized_implies_bounded_range val_size max_hash_size f m γ1 idx x $$ H
  ipureintro
  exact Hx

/-- Rocq: `wp_init_hash_amortized`. -/
theorem wp_init_hash_amortized (E : CoPset) :
    {{ True }} cpl(&(init_hash val_size) #()) @ E
    {{ f, RET f; (|={E}=> ∃ γ1 γ2,
        coll_free_hashfun_amortized val_size max_hash_size f ∅ γ1 γ2 ∗
        iOwn (F := constOF (Auth ℕ)) γ1 (◯ max_hash_size) : IProp GF) }} := by
  iintro %Φ - HΦ
  wp_apply wp_init_hash val_size E $$ [] with %f ⟨%γ2, H⟩
  · itrivial
  iapply HΦ
  imod ErrorCredit.zero (GF := GF) with Hz
  imod H
  have hv : ✓ ((● max_hash_size : Auth ℕ) • ◯ (0 + max_hash_size)) :=
    Auth.auth_both_valid_2 trivial ⟨0, by simp [CMRA.op]; rfl⟩
  imod iOwn_alloc (GF := GF) (F := constOF (Auth ℕ)) _ hv with ⟨%γ1, Hown⟩
  icases iOwn_op.1 $$ Hown with ⟨Hauth, Hfrag⟩
  icases (own_frag_add γ1 0 max_hash_size).1 $$ Hfrag with ⟨H0, Hmax⟩
  imodintro
  iexists γ1, γ2
  iframe Hmax
  unfold coll_free_hashfun
  icases H with ⟨H, Hview⟩
  unfold coll_free_hashfun_amortized hashfun_amortized
  iframe Hview
  iexists 0, 0
  iframe
  ipureintro
  simp

/-- Rocq: `hashfun_amortized_hashfun`. -/
theorem hashfun_amortized_hashfun (f : val) (m : hmap) (γ : GName) :
    ⊢@{IProp GF} hashfun_amortized val_size max_hash_size f m γ -∗ hashfun val_size f m := by
  unfold hashfun_amortized
  iintro ⟨%k, %ε, H, -⟩
  iexact H

/-- Rocq: `wp_hashfun_prev_amortized`. -/
theorem wp_hashfun_prev_amortized (E : CoPset) (f : val) (m : hmap) (γ : GName) (n b : ℕ)
    (Hlookup : m[n]? = some b) :
    {{ hashfun_amortized val_size max_hash_size f m γ }} cpl(&f #n) @ E
    {{ RET LitV (LitInt (b : ℤ));
        (hashfun_amortized val_size max_hash_size f m γ : IProp GF) }} := by
  unfold hashfun_amortized
  iintro %Φ ⟨%k, %ε, Hhash, %Hk, Hrest⟩ HΦ
  wp_apply wp_hashfun_prev val_size E f m n b Hlookup $$ Hhash with H
  iapply HΦ
  iexists k, ε
  iframe
  ipureintro
  exact Hk

/-- Rocq: `wp_coll_free_hashfun_prev_amortized`. -/
theorem wp_coll_free_hashfun_prev_amortized (E : CoPset) (f : val) (m : hmap) (γ1 γ2 : GName)
    (n b : ℕ) (Hlookup : m[n]? = some b) :
    {{ coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2 }} cpl(&f #n) @ E
    {{ RET LitV (LitInt (b : ℤ));
        (coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2 ∗
          hash_view_frag n b γ2 : IProp GF) }} := by
  unfold coll_free_hashfun_amortized
  iintro %Φ ⟨H, Hauth⟩ HΦ
  imod hash_view_auth_duplicate_frag m n b γ2 Hlookup $$ Hauth with ⟨Hauth, Hfrag⟩
  wp_apply wp_hashfun_prev_amortized val_size max_hash_size E f m γ1 n b Hlookup $$ H with H
  iapply HΦ
  iframe

/-- Rocq: `wp_coll_free_hashfun_prev_frag_amortized`. -/
theorem wp_coll_free_hashfun_prev_frag_amortized (E : CoPset) (f : val) (m : hmap)
    (γ1 γ2 : GName) (n b : ℕ) :
    {{ coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2 ∗ hash_view_frag n b γ2 }}
      cpl(&f #n) @ E
    {{ RET LitV (LitInt (b : ℤ));
        (coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2 : IProp GF) }} := by
  iintro %Φ ⟨H, #H'⟩ HΦ
  unfold coll_free_hashfun_amortized
  icases H with ⟨H1, H2⟩
  ihave %Hlk := hash_view_auth_frag_agree m γ2 n b $$ [H2 H']
  · isplitl [H2]
    · iexact H2
    · iexact H'
  iapply wp_coll_free_hashfun_prev_amortized val_size max_hash_size E f m γ1 γ2 n b Hlk
    $$ [H1 H2]
  · unfold coll_free_hashfun_amortized
    iframe
  iintro !> H
  unfold coll_free_hashfun_amortized
  icases H with ⟨⟨H1, H2⟩, -⟩
  iapply HΦ
  iframe

/-- Rocq: `amortized_inequality`. In `ℝ≥0∞` nonnegativity is trivial; the content of the Rocq
lemma (that the subtraction does not truncate for `k ≤ max_hash_size`) is
`amortized_eps_closed`. -/
theorem amortized_inequality (k : ℕ) (_H : k ≤ max_hash_size) :
    0 ≤ (((max_hash_size : ℝ≥0∞) - 1) * k / 2 - ∑ x ∈ Finset.range k, (x : ℝ≥0∞)) /
      ((val_size : ℝ≥0∞) + 1) :=
  bot_le

/-- Rocq: `hashfun_amortized_token_ineq`. -/
theorem hashfun_amortized_token_ineq (f : val) (m : hmap) (γ : GName) :
    ⊢@{IProp GF} hashfun_amortized val_size max_hash_size f m γ -∗
      iOwn (F := constOF (Auth ℕ)) γ (◯ 1) -∗ ⌜m.size < max_hash_size⌝ := by
  unfold hashfun_amortized
  iintro ⟨%k, %ε, -, %Hk, -, -, H1, H3⟩ H2
  subst Hk
  ihave H2 := (own_frag_add γ 1 m.size).2 $$ [H2 H3]
  · isplitl [H2]
    · iexact H2
    · iexact H3
  icases (iOwn_cmraValid_op (GF := GF) (F := constOF (Auth ℕ)) (γ := γ)
      (a1 := (● max_hash_size : Auth ℕ)) (a2 := ◯ (1 + m.size))) $$ [H1 H2] with %Hv
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ipureintro
  obtain ⟨⟨z, hz⟩, -⟩ := Auth.auth_both_valid_discrete.mp Hv
  change max_hash_size = 1 + m.size + z at hz
  omega

/-- Rocq: `wp_insert_new_amortized`. -/
theorem wp_insert_new_amortized (max_hash_size_pos : 0 < max_hash_size) (E : CoPset) (f : val)
    (m : hmap) (γ1 γ2 : GName) (n : ℕ) (Hlookup : m[n]? = none)
    (Hineq : m.size < max_hash_size) :
    {{ coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2 ∗
        ↯ (amortized_error val_size max_hash_size max_hash_size_pos) ∗
        iOwn (F := constOF (Auth ℕ)) γ1 (◯ 1) }}
      cpl(&f #n) @ E
    {{ (v : ℕ), RET LitV (LitInt (v : ℤ));
        (coll_free_hashfun_amortized val_size max_hash_size f (m.insert n v) γ1 γ2 ∗
          hash_view_frag n v γ2 : IProp GF) }} := by
  unfold coll_free_hashfun_amortized
  iintro %Φ ⟨⟨Hhash, Hview⟩, Herr, Htoken⟩ HΦ
  unfold hashfun_amortized
  icases Hhash with ⟨%k, %ε, H, %Hk, %H0, Herr', Hauth, Hfrag⟩
  subst Hk H0
  have Heq : amortized_error val_size max_hash_size max_hash_size_pos +
      amortized_eps val_size max_hash_size m.size =
      (m.toList.length : ℝ≥0∞) / ((val_size + 1 : ℕ) : ℝ≥0∞) +
        amortized_eps val_size max_hash_size (m.size + 1) := by
    rw [Std.ExtTreeMap.length_toList]
    exact amortized_step val_size max_hash_size max_hash_size_pos m.size Hineq
  have Heq' : amortized_error val_size max_hash_size max_hash_size_pos +
      (((max_hash_size : ℝ≥0∞) - 1) * (m.size : ℕ) / 2 -
        ∑ x ∈ Finset.range m.size, (x : ℝ≥0∞)) / ((val_size : ℝ≥0∞) + 1) =
      (m.toList.length : ℝ≥0∞) / ((val_size + 1 : ℕ) : ℝ≥0∞) +
        amortized_eps val_size max_hash_size (m.size + 1) := Heq
  ihave Herr := ErrorCredit.combine $$ [Herr Herr']
  · isplitl [Herr]
    · iexact Herr
    · iexact Herr'
  ihave Herr : ↯ ((m.toList.length : ℝ≥0∞) / ((val_size + 1 : ℕ) : ℝ≥0∞) +
      amortized_eps val_size max_hash_size (m.size + 1)) $$ [Herr]
  · iapply ErrorCredit.ext Heq'
    iexact Herr
  icases ErrorCredit.split $$ Herr with ⟨Hε, Herr⟩
  wp_apply wp_insert_no_coll val_size E f m n γ2 Hlookup $$ [H Hε Hview] with %v ⟨H, Hfrag'⟩
  · unfold coll_free_hashfun
    iframe
  unfold coll_free_hashfun
  icases H with ⟨H, Hview⟩
  iapply HΦ
  iframe Hview Hfrag'
  have Hsize : (m.insert n v).size = m.size + 1 := by
    rw [Std.ExtTreeMap.size_insert]
    have : m.contains n = false := by
      rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, Hlookup]; rfl
    simp [this]
  iexists m.size + 1, amortized_eps val_size max_hash_size (m.size + 1)
  iframe
  ihave Hfrag := (own_frag_add γ1 m.size 1).2 $$ [Hfrag Htoken]
  · isplitl [Hfrag]
    · iexact Hfrag
    · iexact Htoken
  iframe
  ipureintro
  exact ⟨Hsize.symm, rfl⟩

/-- Rocq: `wp_insert_amortized`. -/
theorem wp_insert_amortized (max_hash_size_pos : 0 < max_hash_size) (E : CoPset) (f : val)
    (m : hmap) (γ1 γ2 : GName) (n : ℕ) :
    {{ coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2 ∗
        ↯ (amortized_error val_size max_hash_size max_hash_size_pos) ∗
        iOwn (F := constOF (Auth ℕ)) γ1 (◯ 1) }}
      cpl(&f #n) @ E
    {{ (v : ℕ), RET LitV (LitInt (v : ℤ));
        (∃ m' : hmap, coll_free_hashfun_amortized val_size max_hash_size f m' γ1 γ2 ∗
          ⌜m'[n]? = some v⌝ ∗ ⌜m'.size ≤ m.size + 1⌝ ∗
          ⌜∀ k x : ℕ, m[k]? = some x → m'[k]? = some x⌝ ∗ hash_view_frag n v γ2 : IProp GF) }} := by
  iintro %Φ ⟨Hh, Herr, Hfrag⟩ HΦ
  ihave %Hlt := hashfun_amortized_token_ineq val_size max_hash_size f m γ1 $$ [Hh] [Hfrag]
  · unfold coll_free_hashfun_amortized
    icases Hh with ⟨Hh, -⟩
    iexact Hh
  · iexact Hfrag
  cases Heq : m[n]? with
  | some b =>
    wp_apply wp_coll_free_hashfun_prev_amortized val_size max_hash_size E f m γ1 γ2 n b Heq
      $$ Hh with ⟨H, Hf⟩
    iapply HΦ
    iexists m
    iframe
    ipureintro
    exact ⟨Heq, by omega, fun _ _ h => h⟩
  | none =>
    wp_apply wp_insert_new_amortized val_size max_hash_size max_hash_size_pos E f m γ1 γ2 n Heq
      Hlt $$ [Hh Herr Hfrag] with %v ⟨H, Hf⟩
    · iframe
    iapply HΦ
    iexists m.insert n v
    iframe
    ipureintro
    refine ⟨Std.ExtTreeMap.getElem?_insert_self, ?_, ?_⟩
    · rw [Std.ExtTreeMap.size_insert]; split <;> omega
    · intro k x hk
      rw [Std.ExtTreeMap.getElem?_insert]
      have : compare n k ≠ .eq := by
        intro h
        have : n = k := by simpa using h
        subst this
        rw [Heq] at hk
        cases hk
      simp [this, hk]

end amortized_hash

end Coneris.Examples.Hash
