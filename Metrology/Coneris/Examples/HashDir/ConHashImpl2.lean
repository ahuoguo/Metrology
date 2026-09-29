module

public import Metrology.Coneris.Examples.HashDir.ConHashImpl1
public import Metrology.Coneris.Examples.HashDir.ConHashInterface2
public import Metrology.Coneris.Examples.HashDir.CollFreeHashViewInterface

/-!
# A concurrent hash implementation (version 2), on top of version 1

Ported from clutch/theories/coneris/examples/hash/con_hash_impl2.v

## Rocq → Lean mapping
* Section `con_hash_impl2`: the section variable `val_size` is explicit; the context
  `Hc: conerisGS Σ, h : @hash_view Σ Hc, Hhv: hvG Σ, Hs: !ghost_mapG Σ nat (),
  hash1: !con_hash1 val_size` is `[conerisGS GF] [h : hash_view GF] (Hhv : h.hvG GF)
  [Hs : GhostMapG GF ℕ Unit nat_map] [hash1 : con_hash1 GF val_size]`, where `hash_view` is
  the collision-free `CollFreeHashViewInterface.hash_view` (its ghost-state assumption is an
  explicit argument `Hhv`).
* Programs (same names): `init_hash := init_hash1`, `compute_hash := compute_hash1`,
  `allocate_tape := allocate_tape1`.
* Predicates (same names): `hash_set_frag`, `hash_set`, `hash_auth`, `hash_tape`, `hash_frag`,
  `con_hash_inv`.
  - `v ↪[γ] ()` is `γ ↪◯MAP[v] ()`, `ghost_map_auth γ' 1 m` is `γ' ↪●MAP m`;
    `gset_to_gmap () s` is `ConHashImpl1.gset_to_gmap s`; `size s` is `s.card`.
  - `[∗ map] v ∈ m, P v` (the key unused) is `[∗map] _k ↦ v ∈ m, P v`.
  - As in `ConHashImpl1`, Rocq's `con_hash_inv N f l hm R γ1 γ2 γ_tape γ4 γ5 γ_lock` is
    stated with all its arguments.
* Lemmas (same names): `hash_tape_presample`, `con_hash_init`, `con_hash_alloc_tape`,
  `con_hash_spec`.
  - `hash_tape_presample`: as in `ConHashInterface2`, the Rocq hypothesis
    `INR s + εO * (val_size + 1 - INR s) <= ε * (val_size + 1)` (with `ε εO : nonnegreal`)
    is stated in the subtraction-free form
    `s + εO * (val_size + 1) ≤ ε * (val_size + 1) + εO * s` together with `εO ≠ ∞`. The
    instantiation of `con_hash_interface1.hash_tape_presample` with `bad := s'`, `εI := 1`
    needs `1 * size s' + εO * (val_size + 1 - size s') ≤ ε * (val_size + 1)` (truncated
    `ℝ≥0∞` subtraction); it is derived by the helper `presample_ineq` from the hypothesis and
    `size s' ≤ val_size + 1` (every element of `s'` is `≤ val_size`, by `hash_set_valid`),
    under which the truncated subtraction is the real one.
  - Rocq's `ec_contradict` is `ErrorCredit.contradict`.
* `Program Definition con_hash_impl2 : con_hash2 val_size` is the definition `con_hash_impl2`
  (not an instance, as in Rocq), taking `Hhv` explicitly. Its `Next Obligation`s are the
  lemmas `con_hash_impl2_hash_auth_exclusive`, `con_hash_impl2_hash_auth_frag_agree`,
  `con_hash_impl2_hash_auth_duplicate`, `con_hash_impl2_hash_auth_coll_free`,
  `con_hash_impl2_hash_frag_frag_agree`, `con_hash_impl2_hash_auth_insert`,
  `con_hash_impl2_hash_tape_valid`, `con_hash_impl2_hash_tape_exclusive` (in this order); the
  timeless/persistent obligations (solved automatically in Rocq) are the instances
  `hash_tape_timeless`, `hash_auth_timeless`, etc.
  - In `con_hash_impl2_hash_auth_coll_free`, the `coll_free` of the hash view
    (`CollFreeHashViewInterface.coll_free`) and the one of `con_hash_interface2`
    (`ConHashInterface2.coll_free`) are two definitions with the same body (as in Rocq, where
    `con_hash_interface2` redefines it).
  - In `con_hash_impl2_hash_auth_insert`, the Rocq `iAssert (⌜v ∉ (map_to_list m).*2⌝)` is the
    helper `elem_not_in_values`, and its `Forall (λ x, v ≠ x) ...` is
    `∀ y ∈ m.toList.map (fun p => p.2), v ≠ y`.

## Added
* `presample_ineq`, `elem_not_in_values`, `auth1_set_frags` (the `big_sepM_forall` step of
  `con_hash_spec`).

## Omitted
* The commented-out `∗ [∗ list] n∈ns, hash_set_frag n γ5` in `hash_tape`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map nat_map_insert_eq)
open Coneris.Examples.HashDir.CollFreeHashViewInterface (hash_view)
open Coneris.Examples.HashDir.ConHashInterface1 Coneris.Examples.HashDir.ConHashInterface2
open Coneris.Examples.HashDir.ConHashImpl1 (gset_to_gmap gset_to_gmap_getElem? gset_to_gmap_empty
  gset_to_gmap_union_singleton)

namespace Coneris.Examples.HashDir.ConHashImpl2

/-- Helper: the error inequality of `hash_tape_presample` (see the file docstring). -/
theorem presample_ineq (V c ε εO : ℝ≥0∞) (hc : c ≤ V) (hcfin : c ≠ ∞) (HεO : εO ≠ ∞)
    (Hineq : c + εO * V ≤ ε * V + εO * c) : 1 * c + εO * (V - c) ≤ ε * V := by
  have hfin : εO * c ≠ ∞ := ENNReal.mul_ne_top HεO hcfin
  apply (ENNReal.add_le_add_iff_right hfin).1
  calc 1 * c + εO * (V - c) + εO * c = c + εO * ((V - c) + c) := by ring
    _ = c + εO * V := by rw [tsub_add_cancel_of_le hc]
    _ ≤ ε * V + εO * c := Hineq

section con_hash_impl2

variable (val_size : ℕ)
variable {GF : BundledGFunctors} [Hc : conerisGS GF] [h : hash_view GF] (Hhv : h.hvG GF)
  [Hs : GhostMapG GF ℕ Unit nat_map] [hash1 : con_hash1 GF val_size]

/-- Helper (the Rocq `iAssert (⌜v ∉ (map_to_list m).*2⌝)` of `hash_auth_insert`): an exclusive
element `v` of the ghost map is not among the values of `m`. -/
theorem elem_not_in_values (m : hmap) (v : ℕ) (γ5 : GName) :
    (γ5 ↪◯MAP[v] ()) ∗ ([∗map] _k ↦ x ∈ m, γ5 ↪◯MAP[x] ()) ⊢@{IProp GF}
      ⌜∀ y ∈ m.toList.map (fun p => p.2), v ≠ y⌝ := by
  classical
  by_cases hφ : ∀ y ∈ m.toList.map (fun p => p.2), v ≠ y
  · iintro -
    ipureintro
    exact hφ
  · push Not at hφ
    obtain ⟨y, hy, rfl⟩ := hφ
    obtain ⟨⟨k, y'⟩, hp, rfl⟩ := List.mem_map.1 hy
    have hk : m[k]? = some y' := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hp
    iintro ⟨H2, H6⟩
    ihave H4 := (BigSepM.bigSepM_lookup (M := nat_map)
      (Φ := fun _ x => iprop(γ5 ↪◯MAP[x] ())) (i := k) (x := y') hk) $$ H6
    ihave %Hne := ghost_map_elem_ne (H := nat_map) γ5 y' y' (DFrac.own 1) () () $$ H2 H4
    exact absurd rfl Hne

/-! ## Code -/

/-- Rocq: `init_hash`. -/
def init_hash : val := hash1.init_hash1
/-- Rocq: `compute_hash`. -/
def compute_hash : val := hash1.compute_hash1
/-- Rocq: `allocate_tape`. -/
def allocate_tape : val := hash1.allocate_tape1

/-! ## Predicates -/

/-- Rocq: `hash_set_frag`. -/
def hash_set_frag (v : ℕ) (γ_set : hash1.hash_set_gname) (γ_set' : GName) : IProp GF :=
  iprop(hash1.hash_set_frag1 v γ_set ∗ (γ_set' ↪◯MAP[v] ()))

/-- Rocq: `hash_set`. -/
def hash_set (n : ℕ) (γ : hash1.hash_set_gname) (γ' : GName) : IProp GF :=
  iprop(∃ s : Finset ℕ, ⌜s.card = n⌝ ∗ hash1.hash_set1 s γ ∗ (γ' ↪●MAP gset_to_gmap s))

/-- Rocq: `hash_auth`. -/
def hash_auth (m : hmap) (γ1 : hash1.hash_view_gname) (γ2 : hash1.hash_set_gname)
    (γ4 : h.hv_name) (γ5 : GName) : IProp GF :=
  iprop(h.hv_auth Hhv m γ4 ∗ hash1.hash_auth1 m γ1 γ2 ∗
    [∗map] _k ↦ v ∈ m, hash_set_frag val_size v γ2 γ5)

/-- Rocq: `hash_tape`. -/
def hash_tape (α : val) (ns : List ℕ) (γ2 : hash1.hash_set_gname)
    (γ_tape : hash1.hash_tape_gname) : IProp GF :=
  hash1.hash_tape1 α ns γ2 γ_tape

/-- Rocq: `hash_frag`. -/
def hash_frag (k v : ℕ) (γ1 : hash1.hash_view_gname) (γ2 : hash1.hash_set_gname)
    (γ4 : h.hv_name) : IProp GF :=
  iprop(h.hv_frag Hhv k v γ4 ∗ hash1.hash_frag1 k v γ1 γ2)

instance hash_set_frag_timeless (v : ℕ) (γ_set : hash1.hash_set_gname) (γ_set' : GName) :
    Timeless (hash_set_frag val_size v γ_set γ_set' : IProp GF) := by
  unfold hash_set_frag; infer_instance

instance hash_set_timeless (n : ℕ) (γ : hash1.hash_set_gname) (γ' : GName) :
    Timeless (hash_set val_size n γ γ' : IProp GF) := by
  unfold hash_set; infer_instance

instance hash_auth_timeless (m : hmap) (γ1 : hash1.hash_view_gname) (γ2 : hash1.hash_set_gname)
    (γ4 : h.hv_name) (γ5 : GName) : Timeless (hash_auth val_size Hhv m γ1 γ2 γ4 γ5) := by
  unfold hash_auth; infer_instance

instance hash_tape_timeless (α : val) (ns : List ℕ) (γ2 : hash1.hash_set_gname)
    (γ_tape : hash1.hash_tape_gname) : Timeless (hash_tape val_size α ns γ2 γ_tape) := by
  unfold hash_tape; infer_instance

instance hash_frag_timeless (k v : ℕ) (γ1 : hash1.hash_view_gname) (γ2 : hash1.hash_set_gname)
    (γ4 : h.hv_name) : Timeless (hash_frag val_size Hhv k v γ1 γ2 γ4) := by
  unfold hash_frag; infer_instance

instance hash_frag_persistent (k v : ℕ) (γ1 : hash1.hash_view_gname) (γ2 : hash1.hash_set_gname)
    (γ4 : h.hv_name) : Persistent (hash_frag val_size Hhv k v γ1 γ2 γ4) := by
  unfold hash_frag; infer_instance

/-- Rocq: `con_hash_inv`. -/
def con_hash_inv (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash1.hash_view_gname) (γ2 : hash1.hash_set_gname)
    (γ_tape : hash1.hash_tape_gname) (γ4 : h.hv_name) (γ5 : GName)
    (γ_lock : hash1.hash_lock_gname) : IProp GF :=
  hash1.con_hash_inv1 N f l hm
    (fun m => iprop(h.hv_auth Hhv m γ4 ∗ ([∗map] _k ↦ v ∈ m, γ5 ↪◯MAP[v] ()) ∗ R m))
    γ1 γ2 γ_tape γ_lock

instance con_hash_inv_persistent (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash1.hash_view_gname) (γ2 : hash1.hash_set_gname)
    (γ_tape : hash1.hash_tape_gname) (γ4 : h.hv_name) (γ5 : GName)
    (γ_lock : hash1.hash_lock_gname) :
    Persistent (con_hash_inv val_size Hhv N f l hm R γ1 γ2 γ_tape γ4 γ5 γ_lock) := by
  unfold con_hash_inv; infer_instance

/-! ## Lemmas -/

/-- Rocq: `hash_tape_presample`. -/
theorem hash_tape_presample (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_hv : hash1.hash_view_gname) (γ_set : hash1.hash_set_gname)
    (γ_hv' : h.hv_name) (γ : hash1.hash_tape_gname) (γ_set' : GName)
    (γ_lock : hash1.hash_lock_gname) (α : val) (ns : List ℕ) (s : ℕ) (ε εO : ℝ≥0∞)
    (E : CoPset) (Hsubset : ↑N ⊆ E) (HεO : εO ≠ ∞)
    (Hineq : (s : ℝ≥0∞) + εO * ((val_size : ℝ≥0∞) + 1) ≤
      ε * ((val_size : ℝ≥0∞) + 1) + εO * s) :
    ⊢ con_hash_inv val_size Hhv N f l hm R γ_hv γ_set γ γ_hv' γ_set' γ_lock -∗
      hash_tape val_size α ns γ_set γ -∗ ↯ ε -∗
      hash_set val_size s γ_set γ_set' -∗
      state_update E E iprop(∃ n : Fin (val_size + 1),
        (hash_set val_size (s + 1) γ_set γ_set' ∗ ↯ εO) ∗
        hash_tape val_size α (ns ++ [(n : ℕ)]) γ_set γ ∗
        hash_set_frag val_size (n : ℕ) γ_set γ_set') := by
  classical
  unfold hash_tape hash_set hash_set_frag
  iintro #Hinv Ht Herr ⟨%s', %Hs', Hset, Hset'⟩
  subst Hs'
  ihave ⟨Hset, %Hbound⟩ := persistent_entails_left
    (wand_entails (hash1.hash_set_valid s' γ_set)) $$ Hset
  have hcard : (s'.card : ℝ≥0∞) ≤ (val_size : ℝ≥0∞) + 1 := by
    have : s'.card ≤ val_size + 1 := by
      have := Finset.card_le_card (s := s') (t := Finset.range (val_size + 1))
        (fun x hx => Finset.mem_range.2 (Nat.lt_succ_of_le (Hbound x hx)))
      simpa using this
    exact_mod_cast this
  have Hineq' := presample_ineq ((val_size : ℝ≥0∞) + 1) (s'.card : ℝ≥0∞) ε εO hcard
    (ENNReal.natCast_ne_top _) HεO Hineq
  unfold con_hash_inv
  imod hash1.hash_tape_presample N f l hm _ γ_hv γ_set γ γ_lock α ns s' s' ε 1 εO E Hsubset
    (fun x hx => Nat.lt_succ_of_le (Hbound x hx)) Hineq' $$ Hinv Ht Herr Hset
    with ⟨%n, Herr, Hset, Ht⟩
  icases Herr with (⟨%_, Herr⟩ | ⟨%Hn, Herr⟩)
  · iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Herr
  have Hlk : get? (gset_to_gmap s') (n : ℕ) = none := by
    show (gset_to_gmap s')[(n : ℕ)]? = none
    rw [gset_to_gmap_getElem?]
    simp [Hn]
  imod ghost_map_insert (H := nat_map) (n : ℕ) () Hlk $$ Hset' with ⟨Hset', Hs'⟩
  rw [gset_to_gmap_union_singleton]
  ihave ⟨Hset, #Hfrag⟩ := persistent_entails_left
    (wand_entails (hash1.hash_set_duplicate (n : ℕ) (s' ∪ {(n : ℕ)}) γ_set
      (Finset.mem_union_right _ (Finset.mem_singleton_self _)))) $$ Hset
  imodintro
  iexists n
  iframe Ht Hfrag Hs' Herr
  iexists s' ∪ {(n : ℕ)}
  iframe Hset Hset'
  ipureintro
  rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 Hn),
    Finset.card_singleton]

/-- Rocq: `con_hash_init`. -/
theorem con_hash_init (N : Namespace) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] :
    {{ R ∅ }} cpl(&(init_hash val_size) #())
    {{ (f : val), RET f; ∃ l hm γ1 γ2 γ3 γ4 γ5 γ_lock,
        con_hash_inv val_size Hhv N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock ∗
        hash_set val_size 0 γ2 γ5 }} := by
  iintro %Φ HP HΦ
  unfold init_hash
  iapply fupd_pgl_wp
  imod h.hv_auth_init Hhv with ⟨%γ1', H⟩
  imod ghost_map_alloc_empty (GF := GF) (K := ℕ) (V := Unit) (H := nat_map) with ⟨%γ2', H'⟩
  imodintro
  wp_apply hash1.con_hash_init1 N
    (fun m => iprop(h.hv_auth Hhv m γ1' ∗ ([∗map] _k ↦ v ∈ m, γ2' ↪◯MAP[v] ()) ∗ R m))
    $$ [HP H] with %f ⟨%l, %hm, %γ1, %γ2, %γ3, %γ_lock, #H1, H2⟩
  · iframe HP H
    iapply (BigSepM.bigSepM_empty (M := nat_map)).2
    iempintro
  iapply HΦ
  unfold con_hash_inv hash_set
  iexists l, hm, γ1, γ2, γ3, γ1', γ2', γ_lock
  iframe H1
  iexists ∅
  rw [gset_to_gmap_empty]
  iframe H2 H'
  ipureintro
  rfl

/-- Rocq: `con_hash_alloc_tape`. -/
theorem con_hash_alloc_tape (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash1.hash_view_gname) (γ2 : hash1.hash_set_gname)
    (γ3 : hash1.hash_tape_gname) (γ4 : h.hv_name) (γ5 : GName)
    (γ_lock : hash1.hash_lock_gname) :
    {{ con_hash_inv val_size Hhv N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock }}
      cpl(&(allocate_tape val_size) #())
    {{ (α : val), RET α; hash_tape val_size α [] γ2 γ3 }} := by
  iintro %Φ #Hinv HΦ
  unfold allocate_tape con_hash_inv
  wp_apply hash1.con_hash_alloc_tape1 N f l hm _ γ1 γ2 γ3 γ_lock $$ Hinv with %α H
  iapply HΦ
  unfold hash_tape
  iexact H

/-- Helper (the `big_sepM_forall` step of Rocq's `con_hash_spec`): the values of the map of
`hash_auth1` are in the hash set. -/
theorem auth1_set_frags (m : hmap) (γ1 : hash1.hash_view_gname) (γ2 : hash1.hash_set_gname) :
    hash1.hash_auth1 m γ1 γ2 ⊢
      hash1.hash_auth1 m γ1 γ2 ∗ [∗map] _k ↦ v ∈ m, hash1.hash_set_frag1 v γ2 := by
  refine persistent_entails_left ?_
  refine Entails.trans ?_ (BigSepM.bigSepM_forall (M := nat_map)
    (Φ := fun _ v => hash1.hash_set_frag1 v γ2)).2
  iintro H %k %v %Hk
  ihave Hf := hash1.hash_auth_duplicate m k v γ1 γ2 Hk $$ H
  iapply hash1.hash_frag_in_hash_set γ1 γ2 k v $$ Hf

/-- Rocq: `con_hash_spec`. -/
theorem con_hash_spec (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash1.hash_view_gname) (γ2 : hash1.hash_set_gname)
    (γ3 : hash1.hash_tape_gname) (γ4 : h.hv_name) (γ5 : GName)
    (γ_lock : hash1.hash_lock_gname) (Q1 : ℕ → IProp GF) (Q2 : ℕ → List ℕ → IProp GF)
    (α : val) (v : ℕ) :
    {{ con_hash_inv val_size Hhv N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock ∗
        (∀ m, R m -∗ hash_auth val_size Hhv m γ1 γ2 γ4 γ5 -∗ state_update ⊤ ⊤
          (match m[v]? with
           | some res => iprop(R m ∗ hash_auth val_size Hhv m γ1 γ2 γ4 γ5 ∗ Q1 res)
           | none => iprop(∃ n ns, hash_tape val_size α (n :: ns) γ2 γ3 ∗
                (hash_tape val_size α ns γ2 γ3 ={⊤}=∗ R (m.insert v n) ∗
                  hash_auth val_size Hhv (m.insert v n) γ1 γ2 γ4 γ5 ∗ Q2 n ns)))) }}
      cpl(&f #v &α)
    {{ (res : ℕ), RET LitV (LitInt (res : ℤ)); Q1 res ∨ ∃ ns, Q2 res ns }} := by
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold con_hash_inv
  iapply hash1.con_hash_spec1 N f l hm _ γ1 γ2 γ3 γ_lock Q1 Q2 α v $$ [Hvs]
  · iframe Hinv
    iintro %m ⟨Hhv, Hfrag, HR⟩ Hauth1
    ihave ⟨Hauth1, #Hsf⟩ := auth1_set_frags val_size m γ1 γ2 $$ Hauth1
    unfold hash_auth hash_set_frag
    imod Hvs $$ HR [Hauth1 Hhv Hfrag] with Hcont
    · iframe Hhv Hauth1
      rw [BigSepM.bigSepM_sep_eq]
      iframe Hsf Hfrag
    cases hm' : m[v]? with
    | some res =>
      rw [hm'] at *
      dsimp only
      icases Hcont with ⟨HR, ⟨Hhv, Hauth1, H⟩, HQ⟩
      rw [BigSepM.bigSepM_sep_eq]
      icases H with ⟨-, H⟩
      imodintro
      iframe
    | none =>
      rw [hm'] at *
      dsimp only
      unfold hash_tape
      icases Hcont with ⟨%n, %ns, Ht, Hcont⟩
      imodintro
      iexists n, ns
      iframe Ht
      iintro Ht
      imod Hcont $$ Ht with ⟨HR, ⟨Hhv, Hauth1, H⟩, HQ⟩
      rw [BigSepM.bigSepM_sep_eq]
      icases H with ⟨-, H⟩
      imodintro
      iframe
  iintro !> %res H
  iapply HΦ
  iexact H

/-! ## The obligations of `con_hash_impl2` -/

/-- Rocq: `Next Obligation` 1 of `con_hash_impl2` (`hash_auth_exclusive`). -/
theorem con_hash_impl2_hash_auth_exclusive (m m' : hmap) (γ : hash1.hash_view_gname)
    (γ2 : hash1.hash_set_gname) (γ4 : h.hv_name) (γ5 : GName) :
    ⊢ hash_auth val_size Hhv m γ γ2 γ4 γ5 -∗ hash_auth val_size Hhv m' γ γ2 γ4 γ5 -∗ False := by
  unfold hash_auth
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply h.hv_auth_exclusive Hhv m m' γ4 $$ H1 H2

/-- Rocq: `Next Obligation` 2 of `con_hash_impl2` (`hash_auth_frag_agree`). -/
theorem con_hash_impl2_hash_auth_frag_agree (m : hmap) (k v : ℕ) (γ : hash1.hash_view_gname)
    (γ2 : hash1.hash_set_gname) (γ4 : h.hv_name) (γ5 : GName) :
    ⊢ hash_auth val_size Hhv m γ γ2 γ4 γ5 -∗ hash_frag val_size Hhv k v γ γ2 γ4 -∗
      ⌜m[k]? = some v⌝ := by
  unfold hash_auth hash_frag
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply h.hv_auth_frag_agree Hhv m γ4 k v $$ [H1 H2]
  iframe

/-- Rocq: `Next Obligation` 3 of `con_hash_impl2` (`hash_auth_duplicate`). -/
theorem con_hash_impl2_hash_auth_duplicate (m : hmap) (k v : ℕ) (γ : hash1.hash_view_gname)
    (γ2 : hash1.hash_set_gname) (γ4 : h.hv_name) (γ5 : GName) (Hlk : m[k]? = some v) :
    ⊢ hash_auth val_size Hhv m γ γ2 γ4 γ5 -∗ hash_frag val_size Hhv k v γ γ2 γ4 := by
  unfold hash_auth hash_frag
  iintro ⟨H1, H2, -⟩
  ihave ⟨-, H⟩ := h.hv_auth_duplicate_frag Hhv m k v γ4 Hlk $$ H1
  iframe H
  iapply hash1.hash_auth_duplicate m k v γ γ2 Hlk $$ H2

/-- Rocq: `Next Obligation` 4 of `con_hash_impl2` (`hash_auth_coll_free`). -/
theorem con_hash_impl2_hash_auth_coll_free (m : hmap) (γ : hash1.hash_view_gname)
    (γ2 : hash1.hash_set_gname) (γ4 : h.hv_name) (γ5 : GName) :
    ⊢ hash_auth val_size Hhv m γ γ2 γ4 γ5 -∗ ⌜ConHashInterface2.coll_free m⌝ := by
  unfold hash_auth
  iintro ⟨H, -⟩
  ihave %Hcf := h.hv_auth_coll_free Hhv m γ4 $$ H
  ipureintro
  exact Hcf

/-- Rocq: `Next Obligation` 5 of `con_hash_impl2` (`hash_frag_frag_agree`). -/
theorem con_hash_impl2_hash_frag_frag_agree (k1 k2 v1 v2 : ℕ) (γ : hash1.hash_view_gname)
    (γ2 : hash1.hash_set_gname) (γ4 : h.hv_name) :
    ⊢ hash_frag val_size Hhv k1 v1 γ γ2 γ4 -∗ hash_frag val_size Hhv k2 v2 γ γ2 γ4 -∗
      ⌜k1 = k2 ↔ v1 = v2⌝ := by
  unfold hash_frag
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  iapply h.hv_frag_frag_agree Hhv k1 k2 v1 v2 γ4 $$ H1 H2

/-- Rocq: `Next Obligation` 6 of `con_hash_impl2` (`hash_auth_insert`). -/
theorem con_hash_impl2_hash_auth_insert (m : hmap) (k v : ℕ) (γ1 : hash1.hash_view_gname)
    (γ2 : hash1.hash_set_gname) (γ4 : h.hv_name) (γ5 : GName) (Hlk : m[k]? = none) :
    ⊢ hash_set_frag val_size v γ2 γ5 -∗ hash_auth val_size Hhv m γ1 γ2 γ4 γ5 ==∗
      hash_auth val_size Hhv (m.insert k v) γ1 γ2 γ4 γ5 := by
  unfold hash_set_frag hash_auth hash_set_frag
  iintro ⟨H1, H2⟩ ⟨H3, H4, H5⟩
  rw [BigSepM.bigSepM_sep_eq]
  icases H5 with ⟨#H5, H6⟩
  imod hash1.hash_auth_insert m k v γ1 γ2 Hlk $$ H1 H4 with K
  ihave ⟨K, #Hf⟩ := persistent_entails_left
    (wand_entails (hash1.hash_auth_duplicate (m.insert k v) k v γ1 γ2 (by simp))) $$ K
  ihave ⟨⟨H2, H6⟩, %H0⟩ := persistent_entails_left (elem_not_in_values m v γ5) $$ [H2 H6]
  · iframe H2 H6
  imod h.hv_auth_insert Hhv m k v γ4 Hlk H0 $$ H3 with ⟨H3, -⟩
  imodintro
  iframe H3 K
  rw [← nat_map_insert_eq]
  iapply (BigSepM.bigSepM_insert (M := nat_map)
    (Φ := fun _ v => iprop(hash1.hash_set_frag1 v γ2 ∗ (γ5 ↪◯MAP[v] ()))) Hlk).2
  isplitl [H2]
  · iframe H2
    iapply hash1.hash_frag_in_hash_set γ1 γ2 k v $$ Hf
  rw [BigSepM.bigSepM_sep_eq]
  iframe H5 H6

/-- Rocq: `Next Obligation` 7 of `con_hash_impl2` (`hash_tape_valid`). -/
theorem con_hash_impl2_hash_tape_valid (α : val) (ns : List ℕ) (γ2 : hash1.hash_set_gname)
    (γ3 : hash1.hash_tape_gname) :
    ⊢ hash_tape val_size α ns γ2 γ3 -∗ ⌜∀ x ∈ ns, x ≤ val_size⌝ := by
  unfold hash_tape
  iintro H
  iapply hash1.hash_tape_valid α ns γ2 γ3 $$ H

/-- Rocq: `Next Obligation` 8 of `con_hash_impl2` (`hash_tape_exclusive`). -/
theorem con_hash_impl2_hash_tape_exclusive (α : val) (ns ns' : List ℕ)
    (γ2 : hash1.hash_set_gname) (γ3 : hash1.hash_tape_gname) :
    ⊢ hash_tape val_size α ns γ2 γ3 -∗ hash_tape val_size α ns' γ2 γ3 -∗ False := by
  unfold hash_tape
  iintro H1 H2
  iapply hash1.hash_tape_exclusive α ns ns' γ2 γ3 $$ H1 H2

/-- Rocq: `con_hash_impl2` (a `Program Definition`). -/
@[instance_reducible]
def con_hash_impl2 : con_hash2 GF val_size where
  init_hash2 := init_hash val_size
  allocate_tape2 := allocate_tape val_size
  compute_hash2 := compute_hash val_size
  hash_view_gname := hash1.hash_view_gname
  hash_set_gname := hash1.hash_set_gname
  hash_tape_gname := hash1.hash_tape_gname
  hash_lock_gname := hash1.hash_lock_gname
  hash_view_gname' := h.hv_name
  hash_set_gname' := GName
  con_hash_inv2 N f l hm R _ γ1 γ2 γ3 γ4 γ5 γ_lock :=
    con_hash_inv val_size Hhv N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock
  hash_tape2 := hash_tape val_size
  hash_auth2 := hash_auth val_size Hhv
  hash_frag2 := hash_frag val_size Hhv
  hash_set2 := hash_set val_size
  hash_set_frag2 := hash_set_frag val_size
  hash_tape_timeless := hash_tape_timeless val_size
  hash_auth_timeless := hash_auth_timeless val_size Hhv
  hash_frag_timeless := hash_frag_timeless val_size Hhv
  hash_set_timeless := hash_set_timeless val_size
  hash_set_frag_timeless := hash_set_frag_timeless val_size
  con_hash_inv_persistent N f l hm γ1 γ2 γ3 R _ γ4 γ5 γ_lock :=
    con_hash_inv_persistent val_size Hhv N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock
  hash_frag_persistent := hash_frag_persistent val_size Hhv
  hash_auth_exclusive := con_hash_impl2_hash_auth_exclusive val_size Hhv
  hash_auth_frag_agree := con_hash_impl2_hash_auth_frag_agree val_size Hhv
  hash_auth_duplicate := con_hash_impl2_hash_auth_duplicate val_size Hhv
  hash_auth_coll_free := con_hash_impl2_hash_auth_coll_free val_size Hhv
  hash_frag_frag_agree := con_hash_impl2_hash_frag_frag_agree val_size Hhv
  hash_auth_insert := con_hash_impl2_hash_auth_insert val_size Hhv
  hash_tape_valid := con_hash_impl2_hash_tape_valid val_size
  hash_tape_exclusive := con_hash_impl2_hash_tape_exclusive val_size
  hash_tape_presample N f l hm R _ γ_hv γ_set γ_hv' γ γ_set' γ_lock α ns s ε εO E HN HεO Hineq :=
    hash_tape_presample val_size Hhv N f l hm R γ_hv γ_set γ_hv' γ γ_set' γ_lock α ns s ε εO E
      HN HεO Hineq
  con_hash_init2 N R _ := con_hash_init val_size Hhv N R
  con_hash_alloc_tape2 N f l hm R _ γ1 γ2 γ3 γ4 γ5 γ_lock :=
    con_hash_alloc_tape val_size Hhv N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock
  con_hash_spec2 N f l hm R _ γ1 γ2 γ3 γ4 γ5 γ_lock Q1 Q2 α v :=
    con_hash_spec val_size Hhv N f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock Q1 Q2 α v

end con_hash_impl2

end Coneris.Examples.HashDir.ConHashImpl2
