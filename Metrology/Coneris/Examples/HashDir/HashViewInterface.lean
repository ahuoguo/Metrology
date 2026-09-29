module

public import Metrology.Coneris.ProofMode

/-!
# An interface of a simple hash view

Ported from clutch/theories/coneris/examples/hash/hash_view_interface.v

## Rocq → Lean mapping
* `Class hash_view `{!conerisGS Σ} := Hash_View {...}` is the Lean `class hash_view GF` (over
  `[conerisGS GF]`) with the same field names: `hvG`, `hv_name`, `hv_auth`, `hv_frag`,
  `hv_auth_timeless`, `hv_frag_timeless`, `hv_frag_persistent`, `hv_auth_exclusive`,
  `hv_auth_init`, `hv_auth_duplicate_frag`, `hv_auth_frag_agree`, `hv_frag_frag_agree`,
  `hv_auth_insert`.
  - As in `Coneris.Lib.Lock` / `Coneris.Lib.HocapRand`, the implicit `{L : hvG Σ}` (Rocq finds
    it by type class search) is an explicit argument `(L : hvG GF)`.
  - The instance fields `hv_auth_timeless ::` etc. are fields, re-exported as the global
    instances `hash_view_hv_auth_timeless`, `hash_view_hv_frag_timeless`,
    `hash_view_hv_frag_persistent`.
  - `P -∗ Q` fields are stated as `⊢ P -∗ Q`; `(⊢ |==> ∃ γ, P)%I` is `⊢ |==> ∃ γ, P`.
* `gmap nat nat` is `hmap := Std.ExtTreeMap ℕ ℕ compare` (the helper `nat_map ℕ`), `m !! n` is
  `m[n]?`, `<[n:=x]> m` is `m.insert n x`, `∅` is `∅`.

## Added
* `nat_map` (the finite-map type constructor `gmap nat`, used by iris-lean's ghost maps),
  `hmap` (`gmap nat nat`), `nat_map_insert_eq` (iris-lean's `PartialMap.insert` on `nat_map` is
  `Std.ExtTreeMap.insert`).

## Omitted
* The commented-out Rocq definition `coll_free`.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Coneris

namespace Coneris.Examples.HashDir.HashViewInterface

/-- Helper: finite maps keyed by naturals (Rocq: `gmap nat`). -/
abbrev nat_map : Type → Type := (Std.ExtTreeMap ℕ · compare)

/-- Helper: Rocq's `gmap nat nat`. -/
abbrev hmap : Type := nat_map ℕ

/-- Helper: iris-lean's `PartialMap.insert` on `nat_map` is `Std.ExtTreeMap.insert`. -/
theorem nat_map_insert_eq {V : Type} (m : nat_map V) (k : ℕ) (v : V) :
    Iris.Std.insert m k v = m.insert k v :=
  Std.ExtTreeMap.ext_getElem? fun k' => by
    show (m.alter k (fun _ => some v))[k']? = (m.insert k v)[k']?
    simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_alter]

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
  hv_auth_duplicate_frag (L : hvG GF) (m : hmap) (n b : ℕ) (γ : hv_name) :
    m[n]? = some b → ⊢ hv_auth L m γ -∗ hv_auth L m γ ∗ hv_frag L n b γ
  hv_auth_frag_agree (L : hvG GF) (m : hmap) (γ : hv_name) (k v : ℕ) :
    ⊢ hv_auth L m γ ∗ hv_frag L k v γ -∗ ⌜m[k]? = some v⌝
  hv_frag_frag_agree (L : hvG GF) (γ : hv_name) (k v1 v2 : ℕ) :
    ⊢ hv_frag L k v1 γ -∗ hv_frag L k v2 γ -∗ ⌜v1 = v2⌝
  hv_auth_insert (L : hvG GF) (m : hmap) (n x : ℕ) (γ : hv_name) :
    m[n]? = none → ⊢ hv_auth L m γ ==∗ hv_auth L (m.insert n x) γ ∗ hv_frag L n x γ

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

end Coneris.Examples.HashDir.HashViewInterface
