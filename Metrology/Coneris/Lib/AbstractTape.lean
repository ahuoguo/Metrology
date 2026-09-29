module

public import Metrology.Coneris.PrimitiveLaws
public import Iris.Instances.Lib.GhostMap

/-!
# Abstract tapes

Ported from clutch/theories/coneris/lib/abstract_tape.v

This file describes an auth frag resource algebra specialized for tapes.

## Rocq → Lean mapping
* `abstract_tapesGS Σ := { abstract_tapesGS_inG :: ghost_mapG Σ val (nat * list nat) }` is the
  class `abstract_tapesGS GF` with the instance field
  `abstract_tapesGS_inG : GhostMapG GF val (ℕ × List ℕ) val_map`.
* `abstract_tapesΣ`: superseded by iris-lean's `ElemG` instance search.
* Rocq's `gmap val _` needs `Countable val`. iris-lean's ghost maps need a finite-map type
  constructor: we use `val_map := Std.ExtTreeMap val · compare` (as the Coneris heap uses
  `Std.ExtTreeMap Loc`). For this, `val` gets a linear order, the pull-back of the order on `ℕ`
  along an injective encoding `val → ℕ` (from the derived `Countable val`). The order carries no
  meaning; it is a *scoped* instance (`val_linearOrder`, with `val_lawfulEqCmp`) of this
  namespace, so it does not leak into other files; `open Coneris.Lib.AbstractTape` to reason
  about `val_map`s.
* Notations (scoped): `α ◯↪N ( M ; ns ) @ γ` is `abstract_tapes_frag γ α M ns`
  (= `ghost_map_elem γ (DFrac.own 1) α (M, ns)`, Rocq: `α ↪[γ] (M, ns)`), and `● m @ γ` is
  `abstract_tapes_auth γ m` (= `ghost_map_auth γ (DFrac.own 1) m`), written `●ₐ m @ γ` here
  (the token `●` is taken by iris-lean's authoritative elements).
* `m !! k` is `m[k]?`; `<[k:=v]>m` is `m.insert k v` (bridged to iris-lean's
  `Iris.Std.insert` by the helper `val_map_insert_eq`).
* Lemmas: `abstract_tapes_alloc`, `abstract_tapes_agree`, `abstract_tapes_new`,
  `abstract_tapes_presample`, `abstract_tapes_pop`, `abstract_tapes_notin`,
  `abstract_tapes_auth_exclusive`, `abstract_tapes_frag_exclusive`: same names, stated as
  `⊢ P -∗ Q` (Rocq `P -∗ Q`) or `⊢ P ==∗ Q`.
* `abstract_tapes_notin` is about the (concrete) tape points-to `α ↪N (N; ns)` and a map
  `m : Std.ExtTreeMap Loc (ℕ × List ℕ)` (Rocq infers `gmap loc (nat * list nat)`); it is the same
  statement as the core `hocap_tapes_notin` and proved as it.

## Omitted
* `(** * TODO add*)`: nothing to port.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.AbstractTape

/-! ## Finite maps keyed by values (helpers, see the file docstring) -/

/-- Helper: an injective encoding of values into `ℕ` (from `Countable val`). -/
@[instance_reducible]
def val_encodable : Encodable val := Encodable.ofCountable val

/-- Helper: a (meaningless) linear order on values, used to key `Std.ExtTreeMap`s. -/
scoped instance val_linearOrder : LinearOrder val :=
  letI := val_encodable
  LinearOrder.lift' (Encodable.encode (α := val)) Encodable.encode_injective

scoped instance val_lawfulEqCmp : Std.LawfulEqCmp (compare : val → val → Ordering) where
  eq_of_compare h := compare_eq_iff_eq.1 h
  compare_self := compare_eq_iff_eq.2 rfl

/-- Helper: finite maps keyed by values (Rocq: `gmap val`). -/
abbrev val_map : Type → Type := (Std.ExtTreeMap val · compare)

/-- Helper: iris-lean's `PartialMap.insert` on `val_map` is `Std.ExtTreeMap.insert`. -/
theorem val_map_insert_eq {V : Type} (m : val_map V) (k : val) (v : V) :
    Iris.Std.insert m k v = m.insert k v :=
  Std.ExtTreeMap.ext_getElem? fun k' => by
    show (m.alter k (fun _ => some v))[k']? = (m.insert k v)[k']?
    simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_alter]

/-! ## Ghost state -/

/-- Rocq: `abstract_tapesGS`. -/
class abstract_tapesGS (GF : BundledGFunctors) where
  abstract_tapesGS_inG : GhostMapG GF val (ℕ × List ℕ) val_map

attribute [reducible, instance] abstract_tapesGS.abstract_tapesGS_inG

/-- Rocq: `α ◯↪N ( M ; ns ) @ γ` (the fragment). -/
def abstract_tapes_frag {GF : BundledGFunctors} [abstract_tapesGS GF] (γ : GName) (α : val)
    (M : ℕ) (ns : List ℕ) : IProp GF :=
  ghost_map_elem (H := val_map) γ (DFrac.own 1) α (M, ns)

/-- Rocq: `● m @ γ` (the authoritative part). -/
def abstract_tapes_auth {GF : BundledGFunctors} [abstract_tapesGS GF] (γ : GName)
    (m : val_map (ℕ × List ℕ)) : IProp GF :=
  ghost_map_auth (H := val_map) γ (DFrac.own 1) m

@[inherit_doc abstract_tapes_frag]
scoped notation:20 α:max " ◯↪N " "(" M "; " ns ")" " @ " γ:max => abstract_tapes_frag γ α M ns

@[inherit_doc abstract_tapes_auth]
scoped notation:20 "●ₐ " m:max " @ " γ:max => abstract_tapes_auth γ m

section tapes_lemmas

-- Rocq's `Context` also has `conerisGS Σ`, which only `abstract_tapes_notin` uses.
variable {GF : BundledGFunctors} [abstract_tapesGS GF]

/-- Rocq: `abstract_tapes_alloc`. -/
theorem abstract_tapes_alloc (m : val_map (ℕ × List ℕ)) :
    ⊢@{IProp GF} |==> ∃ γ, (●ₐ m @ γ) ∗ [∗map] k ↦ v ∈ m, (k ◯↪N (v.1; v.2) @ γ) := by
  unfold abstract_tapes_auth abstract_tapes_frag
  imod ghost_map_alloc (GF := GF) (H := val_map) m with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe H1
  iexact H2

/-- Rocq: `abstract_tapes_agree`. -/
theorem abstract_tapes_agree (m : val_map (ℕ × List ℕ)) (γ : GName) (k : val) (N : ℕ)
    (ns : List ℕ) :
    ⊢@{IProp GF} (●ₐ m @ γ) -∗ (k ◯↪N (N; ns) @ γ) -∗ ⌜m[k]? = some (N, ns)⌝ := by
  unfold abstract_tapes_auth abstract_tapes_frag
  iintro H1 H2
  iapply ghost_map_lookup $$ H1 H2

/-- Rocq: `abstract_tapes_new`. -/
theorem abstract_tapes_new (γ : GName) (m : val_map (ℕ × List ℕ)) (k : val) (N : ℕ)
    (ns : List ℕ) (Hlookup : m[k]? = none) :
    ⊢@{IProp GF} (●ₐ m @ γ) ==∗ (●ₐ (m.insert k (N, ns)) @ γ) ∗ (k ◯↪N (N; ns) @ γ) := by
  iintro H
  unfold abstract_tapes_auth abstract_tapes_frag
  rw [← val_map_insert_eq]
  iapply ghost_map_insert k (N, ns) Hlookup $$ H

/-- Rocq: `abstract_tapes_presample`. -/
theorem abstract_tapes_presample (γ : GName) (m : val_map (ℕ × List ℕ)) (k : val) (N : ℕ)
    (ns : List ℕ) (n : ℕ) :
    ⊢@{IProp GF} (●ₐ m @ γ) -∗ (k ◯↪N (N; ns) @ γ) ==∗
      (●ₐ (m.insert k (N, ns ++ [n])) @ γ) ∗ (k ◯↪N (N; ns ++ [n]) @ γ) := by
  iintro H1 H2
  unfold abstract_tapes_auth abstract_tapes_frag
  rw [← val_map_insert_eq]
  iapply ghost_map_update (N, ns ++ [n]) $$ H1 H2

/-- Rocq: `abstract_tapes_pop`. -/
theorem abstract_tapes_pop (γ : GName) (m : val_map (ℕ × List ℕ)) (k : val) (N : ℕ)
    (ns : List ℕ) (n : ℕ) :
    ⊢@{IProp GF} (●ₐ m @ γ) -∗ (k ◯↪N (N; n :: ns) @ γ) ==∗
      (●ₐ (m.insert k (N, ns)) @ γ) ∗ (k ◯↪N (N; ns) @ γ) := by
  iintro H1 H2
  unfold abstract_tapes_auth abstract_tapes_frag
  rw [← val_map_insert_eq]
  iapply ghost_map_update (N, ns) $$ H1 H2

omit [abstract_tapesGS GF] in
/-- Rocq: `abstract_tapes_notin`. -/
theorem abstract_tapes_notin [conerisGS GF] (α : Loc) (N : ℕ) (ns : List ℕ)
    (m : Std.ExtTreeMap Loc (ℕ × List ℕ)) (f : ℕ × List ℕ → ℕ) (g : ℕ × List ℕ → List ℕ) :
    ⊢@{IProp GF} α ↪N (N; ns) -∗ ([∗map] α0 ↦ t ∈ (m : loc_map (ℕ × List ℕ)),
      α0 ↪N (f t; g t)) -∗ ⌜m[α]? = none⌝ := by
  cases Heqn : m[α]? with
  | none =>
    iintro - -
    ipureintro
    rfl
  | some t =>
    iintro Hα Hmap
    ihave Ht := BigSepM.bigSepM_lookup (M := loc_map) (i := α) Heqn $$ Hmap
    iexfalso
    iapply tapeN_tapeN_contradict $$ Hα Ht

/-- Rocq: `abstract_tapes_auth_exclusive`. -/
theorem abstract_tapes_auth_exclusive (m m' : val_map (ℕ × List ℕ)) (γ : GName) :
    ⊢@{IProp GF} (●ₐ m @ γ) -∗ (●ₐ m' @ γ) -∗ False := by
  iintro H1 H2
  unfold abstract_tapes_auth
  ihave %H := ghost_map_auth_valid_2 $$ H1 H2
  exact absurd (DFrac.valid_own_op H.1) (by simp)

/-- Rocq: `abstract_tapes_frag_exclusive`. -/
theorem abstract_tapes_frag_exclusive (k : val) (N N' : ℕ) (ns ns' : List ℕ) (γ : GName) :
    ⊢@{IProp GF} (k ◯↪N (N; ns) @ γ) -∗ (k ◯↪N (N'; ns') @ γ) -∗ False := by
  iintro H1 H2
  unfold abstract_tapes_frag
  ihave ⟨%H, -⟩ := ghost_map_elem_valid_2 $$ [H1 H2]
  · iframe
  exact absurd (DFrac.valid_own_op H) (by simp)

end tapes_lemmas

end Coneris.Lib.AbstractTape
