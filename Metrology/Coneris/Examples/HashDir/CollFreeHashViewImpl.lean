module

public import Metrology.Coneris.Examples.HashDir.CollFreeHashViewInterface
public import Iris.Instances.Lib.SetBij
public import Iris.Std.GenSetsInstances

/-!
# An implementation of a collision-free hash view

Ported from clutch/theories/coneris/examples/hash/coll_free_hash_view_impl.v

## Rocq → Lean mapping
* `gset_bijR nat nat` over `gset (nat * nat)` is iris-lean's `SetBij pairset` with
  `pairset := Std.ExtTreeSet (ℕ × ℕ) compare` (the order on pairs is the lexicographic order,
  the scoped instance `instOrdNatPair`); `inG Σ (gset_bijR nat nat)` is
  `[HinG : SetBijG GF ℕ ℕ pairset]`; `own γ (gset_bij_auth (DfracOwn 1) L)` is `γ ↪●BIJ L`,
  `own γ (gset_bij_elem k v)` is `γ ↪◯BIJ⟨k, v⟩`; `map_to_set pair m` is `map_to_set m`.
  (This is the same encoding as in `Coneris.Examples.Hash`.)
* Section `hash_view_impl`: `hash_view_auth`, `hash_view_frag`, `hash_view_auth_coll_free`,
  `hash_view_auth_duplicate_frag`, `hash_view_auth_frag_agree`, `hash_view_auth_insert`: same
  names, stated as `⊢ P -∗ Q` / `⊢ P ==∗ Q`.
* `hvG1` (with the instance field `hvG1_gsetbijR`) is a Lean class.
* `hv_impl` (Rocq: `Program Definition`) is a definition (not an instance); the
  `Next Obligation`s that are not the section lemmas are the helper theorems
  `hv_impl_hv_auth_exclusive`, `hv_impl_hv_auth_init`, `hv_impl_hv_frag_frag_agree`.

## Added
* `instOrdNatPair`, `pairset`, `map_to_set`, `elem_of_map_to_set_pair` (stdpp's
  `elem_of_map_to_set_pair`), `map_to_set_empty`, `map_to_set_insert` (stdpp's
  `map_to_set_insert_L`): the stdpp map/set infrastructure.
* The timeless/persistent instances `hash_view_auth_timeless`, `hash_view_frag_timeless`,
  `hash_view_frag_persistent` (Rocq obligations solved automatically).

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Examples.HashDir.CollFreeHashViewInterface
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map)

namespace Coneris.Examples.HashDir.CollFreeHashViewImpl

/-! ## Maps and sets of pairs -/

/-- The lexicographic order on pairs (used for `pairset`). -/
scoped instance instOrdNatPair : Ord (ℕ × ℕ) := lexOrd

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

section hash_view_impl

variable {GF : BundledGFunctors} [HinG : SetBijG GF ℕ ℕ pairset]

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

/-- Rocq: `hash_view_auth_coll_free`. -/
theorem hash_view_auth_coll_free (m : hmap) (γ2 : GName) :
    ⊢@{IProp GF} hash_view_auth m γ2 -∗ ⌜coll_free m⌝ := by
  refine entails_wand ?_
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

/-- Rocq: `hash_view_auth_duplicate_frag`. -/
theorem hash_view_auth_duplicate_frag (m : hmap) (n b : ℕ) (γ2 : GName) (Hsome : m[n]? = some b) :
    ⊢@{IProp GF} hash_view_auth m γ2 -∗ hash_view_auth m γ2 ∗ hash_view_frag n b γ2 := by
  refine entails_wand ?_
  unfold hash_view_auth hash_view_frag
  exact persistent_entails_left
    (set_bij_own_elem_get _ _ ((elem_of_map_to_set_pair m n b).mpr Hsome))

/-- Rocq: `hash_view_auth_frag_agree`. -/
theorem hash_view_auth_frag_agree (m : hmap) (γ2 : GName) (k v : ℕ) :
    ⊢@{IProp GF} hash_view_auth m γ2 ∗ hash_view_frag k v γ2 -∗ ⌜m[k]? = some v⌝ := by
  refine entails_wand ?_
  unfold hash_view_auth hash_view_frag
  exact (set_bij_elem_of k v).trans (pure_mono (elem_of_map_to_set_pair m k v).mp)

/-- Rocq: `hash_view_auth_insert`. -/
theorem hash_view_auth_insert (m : hmap) (n x : ℕ) (γ : GName) (H1 : m[n]? = none)
    (H2 : ∀ y ∈ m.toList.map (fun p => p.2), x ≠ y) :
    ⊢@{IProp GF} hash_view_auth m γ ==∗
      hash_view_auth (m.insert n x) γ ∗ hash_view_frag n x γ := by
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

/-- Rocq: first `Next Obligation` of `hv_impl`. -/
theorem hv_impl_hv_auth_exclusive (m m' : hmap) (γ : GName) :
    ⊢@{IProp GF} hash_view_auth m γ -∗ hash_view_auth m' γ -∗ False := by
  unfold hash_view_auth
  iintro H1 H2
  iapply set_bij_own_auth_exclusive $$ [H1 H2]
  iframe

/-- Rocq: second `Next Obligation` of `hv_impl`. -/
theorem hv_impl_hv_auth_init : ⊢@{IProp GF} |==> ∃ γ, hash_view_auth ∅ γ := by
  unfold hash_view_auth
  rw [map_to_set_empty]
  exact set_bij_own_alloc_empty

/-- Rocq: sixth `Next Obligation` of `hv_impl`. -/
theorem hv_impl_hv_frag_frag_agree (k1 k2 v1 v2 : ℕ) (γ : GName) :
    ⊢@{IProp GF} hash_view_frag k1 v1 γ -∗ hash_view_frag k2 v2 γ -∗ ⌜k1 = k2 ↔ v1 = v2⌝ := by
  unfold hash_view_frag
  iintro H1 H2
  iapply set_bij_own_elem_agree $$ [H1 H2]
  iframe

end hash_view_impl

/-- Rocq: `hvG1`. -/
class hvG1 (GF : BundledGFunctors) where
  hvG1_gsetbijR : SetBijG GF ℕ ℕ pairset

attribute [reducible, instance] hvG1.hvG1_gsetbijR

/-- Rocq: `hv_impl` (a `Program Definition`). -/
@[instance_reducible]
def hv_impl {GF : BundledGFunctors} [conerisGS GF] : hash_view GF where
  hvG := hvG1
  hv_name := GName
  hv_auth L m γ := hash_view_auth (HinG := L.hvG1_gsetbijR) m γ
  hv_frag L k v γ := hash_view_frag (HinG := L.hvG1_gsetbijR) k v γ
  hv_auth_timeless L m γ := hash_view_auth_timeless (HinG := L.hvG1_gsetbijR) m γ
  hv_frag_timeless L k v γ := hash_view_frag_timeless (HinG := L.hvG1_gsetbijR) k v γ
  hv_frag_persistent L k v γ := hash_view_frag_persistent (HinG := L.hvG1_gsetbijR) k v γ
  hv_auth_exclusive L := hv_impl_hv_auth_exclusive (HinG := L.hvG1_gsetbijR)
  hv_auth_init L := hv_impl_hv_auth_init (HinG := L.hvG1_gsetbijR)
  hv_auth_coll_free L := hash_view_auth_coll_free (HinG := L.hvG1_gsetbijR)
  hv_auth_duplicate_frag L m n b γ H := hash_view_auth_duplicate_frag (HinG := L.hvG1_gsetbijR)
    m n b γ H
  hv_auth_frag_agree L := hash_view_auth_frag_agree (HinG := L.hvG1_gsetbijR)
  hv_frag_frag_agree L := hv_impl_hv_frag_frag_agree (HinG := L.hvG1_gsetbijR)
  hv_auth_insert L m n x γ H1 H2 := hash_view_auth_insert (HinG := L.hvG1_gsetbijR) m n x γ H1 H2

end Coneris.Examples.HashDir.CollFreeHashViewImpl
