module

public import Metrology.Coneris.Examples.HashDir.HashViewInterface
public import Iris.Instances.Lib.GhostMap

/-!
# An implementation of a hash view

Ported from clutch/theories/coneris/examples/hash/hash_view_impl.v

## Rocq → Lean mapping
* Section `hash_view_impl`: the context `ghost_mapG Σ nat nat` is
  `[HinG : GhostMapG GF ℕ ℕ nat_map]` (iris-lean's ghost maps over `nat_map = gmap nat`).
  `ghost_map_auth γ 1 m` is `γ ↪●MAP m`, `k ↪[γ]□ v` is `γ ↪◯MAP[k]{.discard} v`.
  `hash_view_auth`, `hash_view_frag`, `hash_view_auth_duplicate_frag`,
  `hash_view_auth_frag_agree`, `hash_view_auth_insert`: same names.
  The `P -∗ Q` / `P ==∗ Q` lemmas are stated as `⊢ P -∗ Q` / `⊢ P ==∗ Q`.
* `hvG1` (with the instance field `hvG1_ghost_mapG`) is a Lean class.
* `hv_impl` (Rocq: `Program Definition`) is a definition (not an instance); the
  `Next Obligation`s are the helper theorems `hv_impl_hv_auth_exclusive`,
  `hv_impl_hv_auth_init`, `hv_impl_hv_frag_frag_agree`; the timeless/persistent obligations
  (solved automatically in Rocq) are the instances `hash_view_auth_timeless`,
  `hash_view_frag_timeless`, `hash_view_frag_persistent`.

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Examples.HashDir.HashViewInterface

namespace Coneris.Examples.HashDir.HashViewImpl

section hash_view_impl

variable {GF : BundledGFunctors} [HinG : GhostMapG GF ℕ ℕ nat_map]

/-- Rocq: `hash_view_auth`. -/
def hash_view_auth (m : hmap) (γ : GName) : IProp GF :=
  iprop((γ ↪●MAP m) ∗ [∗map] k ↦ v ∈ m, γ ↪◯MAP[k]{.discard} v)

/-- Rocq: `hash_view_frag`. -/
def hash_view_frag (k v : ℕ) (γ : GName) : IProp GF := γ ↪◯MAP[k]{.discard} v

instance hash_view_auth_timeless (m : hmap) (γ : GName) :
    Timeless (hash_view_auth (GF := GF) m γ) := by
  unfold hash_view_auth; infer_instance

instance hash_view_frag_timeless (k v : ℕ) (γ : GName) :
    Timeless (hash_view_frag (GF := GF) k v γ) := by
  unfold hash_view_frag; infer_instance

instance hash_view_frag_persistent (k v : ℕ) (γ : GName) :
    Persistent (hash_view_frag (GF := GF) k v γ) := by
  unfold hash_view_frag; infer_instance

/-- Rocq: `hash_view_auth_duplicate_frag`. -/
theorem hash_view_auth_duplicate_frag (m : hmap) (n b : ℕ) (γ2 : GName) (Hsome : m[n]? = some b) :
    ⊢@{IProp GF} hash_view_auth m γ2 -∗ hash_view_auth m γ2 ∗ hash_view_frag n b γ2 := by
  unfold hash_view_auth hash_view_frag
  iintro ⟨Hauth, #Hauth'⟩
  iframe Hauth Hauth'
  iapply (BigSepM.bigSepM_lookup (M := nat_map) (i := n) (x := b) Hsome) $$ Hauth'

/-- Rocq: `hash_view_auth_frag_agree`. -/
theorem hash_view_auth_frag_agree (m : hmap) (γ2 : GName) (k v : ℕ) :
    ⊢@{IProp GF} hash_view_auth m γ2 ∗ hash_view_frag k v γ2 -∗ ⌜m[k]? = some v⌝ := by
  unfold hash_view_auth hash_view_frag
  iintro ⟨⟨H1, -⟩, H2⟩
  iapply ghost_map_lookup $$ H1 H2

/-- Rocq: `hash_view_auth_insert`. -/
theorem hash_view_auth_insert (m : hmap) (n x : ℕ) (γ : GName) (H1 : m[n]? = none) :
    ⊢@{IProp GF} hash_view_auth m γ ==∗
      hash_view_auth (m.insert n x) γ ∗ hash_view_frag n x γ := by
  unfold hash_view_auth hash_view_frag
  iintro ⟨Hauth, Hauth'⟩
  imod ghost_map_insert_persist (H := nat_map) n x H1 $$ Hauth with ⟨Hauth, #Hfrag⟩
  imodintro
  rw [← nat_map_insert_eq]
  iframe Hauth Hfrag
  iapply (BigSepM.bigSepM_insert (M := nat_map) (Φ := fun k v => iprop(γ ↪◯MAP[k]{.discard} v))
    H1).2
  iframe Hfrag Hauth'

end hash_view_impl

/-- Rocq: `hvG1`. -/
class hvG1 (GF : BundledGFunctors) where
  hvG1_ghost_mapG : GhostMapG GF ℕ ℕ nat_map

attribute [reducible, instance] hvG1.hvG1_ghost_mapG

section hv_impl

variable {GF : BundledGFunctors} [HinG : GhostMapG GF ℕ ℕ nat_map]

/-- Rocq: first `Next Obligation` of `hv_impl`. -/
theorem hv_impl_hv_auth_exclusive (m m' : hmap) (γ : GName) :
    ⊢@{IProp GF} hash_view_auth m γ -∗ hash_view_auth m' γ -∗ False := by
  unfold hash_view_auth
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  ihave %H := ghost_map_auth_valid_2 $$ H1 H2
  exact absurd (DFrac.valid_own_op H.1) (by simp)

/-- Rocq: second `Next Obligation` of `hv_impl`. -/
theorem hv_impl_hv_auth_init : ⊢@{IProp GF} |==> ∃ γ, hash_view_auth ∅ γ := by
  unfold hash_view_auth
  imod ghost_map_alloc_empty (GF := GF) (K := ℕ) (V := ℕ) (H := nat_map) with ⟨%γ, H⟩
  imodintro
  iexists γ
  iframe H
  iapply (BigSepM.bigSepM_empty (M := nat_map)).2
  itrivial

/-- Rocq: fifth `Next Obligation` of `hv_impl`. -/
theorem hv_impl_hv_frag_frag_agree (γ : GName) (k v1 v2 : ℕ) :
    ⊢@{IProp GF} hash_view_frag k v1 γ -∗ hash_view_frag k v2 γ -∗ ⌜v1 = v2⌝ := by
  unfold hash_view_frag
  iintro H1 H2
  iapply ghost_map_elem_agree $$ [H1 H2]
  iframe

end hv_impl

/-- Rocq: `hv_impl` (a `Program Definition`). -/
@[instance_reducible]
def hv_impl {GF : BundledGFunctors} [conerisGS GF] : hash_view GF where
  hvG := hvG1
  hv_name := GName
  hv_auth L m γ := hash_view_auth (HinG := L.hvG1_ghost_mapG) m γ
  hv_frag L k v γ := hash_view_frag (HinG := L.hvG1_ghost_mapG) k v γ
  hv_auth_timeless L m γ := hash_view_auth_timeless (HinG := L.hvG1_ghost_mapG) m γ
  hv_frag_timeless L k v γ := hash_view_frag_timeless (HinG := L.hvG1_ghost_mapG) k v γ
  hv_frag_persistent L k v γ := hash_view_frag_persistent (HinG := L.hvG1_ghost_mapG) k v γ
  hv_auth_exclusive L := hv_impl_hv_auth_exclusive (HinG := L.hvG1_ghost_mapG)
  hv_auth_init L := hv_impl_hv_auth_init (HinG := L.hvG1_ghost_mapG)
  hv_auth_duplicate_frag L m n b γ H := hash_view_auth_duplicate_frag (HinG := L.hvG1_ghost_mapG)
    m n b γ H
  hv_auth_frag_agree L := hash_view_auth_frag_agree (HinG := L.hvG1_ghost_mapG)
  hv_frag_frag_agree L := hv_impl_hv_frag_frag_agree (HinG := L.hvG1_ghost_mapG)
  hv_auth_insert L m n x γ H := hash_view_auth_insert (HinG := L.hvG1_ghost_mapG) m n x γ H

end Coneris.Examples.HashDir.HashViewImpl
