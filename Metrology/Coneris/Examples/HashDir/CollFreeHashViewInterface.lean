module

public import Metrology.Coneris.Examples.HashDir.HashViewInterface

/-!
# An interface of a collision-free hash view

Ported from clutch/theories/coneris/examples/hash/coll_free_hash_view_interface.v

## Rocq → Lean mapping
* `coll_free` (same name): `is_Some (m !! k)` is `(m[k]?).isSome`, `m !!! k` (lookup with the
  default `inhabitant = 0`) is `m.getD k 0`.
* `Class hash_view `{!conerisGS Σ} := Hash_View {...}` is the Lean `class hash_view GF` (over
  `[conerisGS GF]`) with the same field names: `hvG`, `hv_name`, `hv_auth`, `hv_frag`,
  `hv_auth_timeless`, `hv_frag_timeless`, `hv_frag_persistent`, `hv_auth_exclusive`,
  `hv_auth_init`, `hv_auth_coll_free`, `hv_auth_duplicate_frag`, `hv_auth_frag_agree`,
  `hv_frag_frag_agree`, `hv_auth_insert`. It is a different class from
  `Coneris.Examples.HashDir.HashViewInterface.hash_view` (as in Rocq, where both are called
  `hash_view` in different files).
  - As in `Coneris.Lib.Lock`, the implicit `{L : hvG Σ}` is an explicit argument `(L : hvG GF)`.
  - The instance fields are re-exported as the global instances `hash_view_hv_auth_timeless`,
    `hash_view_hv_frag_timeless`, `hash_view_hv_frag_persistent`.
  - `P -∗ Q` fields are stated as `⊢ P -∗ Q`.
  - `Forall (λ m, x ≠ m) (map (λ p, p.2) (map_to_list m))` is
    `∀ y ∈ m.toList.map (fun p => p.2), x ≠ y`.
* `gmap nat nat` is `hmap` (from `HashViewInterface`), `m !! n` is `m[n]?`, `<[n:=x]> m` is
  `m.insert n x`.

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Coneris
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map)

namespace Coneris.Examples.HashDir.CollFreeHashViewInterface

/-- Rocq: `coll_free`. A hash function is collision free if the partial map it implements is
an injective function. -/
def coll_free (m : hmap) : Prop :=
  ∀ k1 k2, (m[k1]?).isSome → (m[k2]?).isSome → m.getD k1 0 = m.getD k2 0 → k1 = k2

/-- Rocq: `hash_view`. -/
class hash_view (GF : BundledGFunctors) [conerisGS GF] where
  hvG : BundledGFunctors → Type
  hv_name : Type
  hv_auth (L : hvG GF) : hmap → hv_name → IProp GF
  hv_frag (L : hvG GF) : ℕ → ℕ → hv_name → IProp GF
  hv_auth_timeless (L : hvG GF) (m : hmap) (γ : hv_name) : Timeless (hv_auth L m γ)
  hv_frag_timeless (L : hvG GF) (k v : ℕ) (γ : hv_name) : Timeless (hv_frag L k v γ)
  hv_frag_persistent (L : hvG GF) (k v : ℕ) (γ : hv_name) : Persistent (hv_frag L k v γ)
  hv_auth_exclusive (L : hvG GF) (m m' : hmap) (γ : hv_name) :
    ⊢ hv_auth L m γ -∗ hv_auth L m' γ -∗ False
  hv_auth_init (L : hvG GF) : ⊢ |==> ∃ γ, hv_auth L ∅ γ
  hv_auth_coll_free (L : hvG GF) (m : hmap) (γ : hv_name) :
    ⊢ hv_auth L m γ -∗ ⌜coll_free m⌝
  hv_auth_duplicate_frag (L : hvG GF) (m : hmap) (n b : ℕ) (γ : hv_name) :
    m[n]? = some b → ⊢ hv_auth L m γ -∗ hv_auth L m γ ∗ hv_frag L n b γ
  hv_auth_frag_agree (L : hvG GF) (m : hmap) (γ : hv_name) (k v : ℕ) :
    ⊢ hv_auth L m γ ∗ hv_frag L k v γ -∗ ⌜m[k]? = some v⌝
  hv_frag_frag_agree (L : hvG GF) (k1 k2 v1 v2 : ℕ) (γ : hv_name) :
    ⊢ hv_frag L k1 v1 γ -∗ hv_frag L k2 v2 γ -∗ ⌜k1 = k2 ↔ v1 = v2⌝
  hv_auth_insert (L : hvG GF) (m : hmap) (n x : ℕ) (γ : hv_name) :
    m[n]? = none → (∀ y ∈ m.toList.map (fun p => p.2), x ≠ y) →
    ⊢ hv_auth L m γ ==∗ hv_auth L (m.insert n x) γ ∗ hv_frag L n x γ

section instances

variable {GF : BundledGFunctors} [conerisGS GF] [h : hash_view GF]

/-- Rocq: the instance field `hv_auth_timeless`. -/
instance hash_view_hv_auth_timeless (L : h.hvG GF) (m : hmap) (γ : h.hv_name) :
    Timeless (h.hv_auth L m γ) := h.hv_auth_timeless L m γ

/-- Rocq: the instance field `hv_frag_timeless`. -/
instance hash_view_hv_frag_timeless (L : h.hvG GF) (k v : ℕ) (γ : h.hv_name) :
    Timeless (h.hv_frag L k v γ) := h.hv_frag_timeless L k v γ

/-- Rocq: the instance field `hv_frag_persistent`. -/
instance hash_view_hv_frag_persistent (L : h.hvG GF) (k v : ℕ) (γ : h.hv_name) :
    Persistent (h.hv_frag L k v γ) := h.hv_frag_persistent L k v γ

end instances

end Coneris.Examples.HashDir.CollFreeHashViewInterface
