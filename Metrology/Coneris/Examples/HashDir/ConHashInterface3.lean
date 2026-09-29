module

public import Metrology.Coneris.Examples.HashDir.HashViewInterface
public import Metrology.Coneris.ErrorRules
public import Iris.Instances.Lib.Invariants

/-!
# A concurrent hash interface (version 3)

Ported from clutch/theories/coneris/examples/hash/con_hash_interface3.v

## Rocq → Lean mapping
* `coll_free` (same name; Rocq redefines it in this file): `is_Some (m !! k)` is
  `(m[k]?).isSome`, `m !!! k` is `m.getD k 0`.
* `amortized_error` (Rocq: a `Program Definition` into `nonnegreal`, whose obligation uses the
  positivity hypothesis) is `((max_hash_size : ℝ≥0∞) - 1) / (2 * ((val_size : ℝ≥0∞) + 1))`;
  the truncated `ℝ≥0∞` subtraction does not truncate since `0 < max_hash_size`.
* `Class con_hash3 `{!conerisGS Σ} (val_size:nat) (max_hash_size:nat) (Hpos:0<max_hash_size)`
  is the Lean `class con_hash3 GF [conerisGS GF] (val_size max_hash_size : ℕ)
  (Hpos : 0 < max_hash_size)` with the same field names:
  `init_hash3`, `allocate_tape3`, `compute_hash3`, `hash_view_gname`, `hash_set_gname`,
  `hash_tape_gname`, `hash_lock_gname`, `hash_view_gname'`, `hash_set_gname'`,
  `hash_token_gname`, `con_hash_inv3`, `hash_tape3`, `hash_auth3`, `hash_frag3`, `hash_set3`,
  `hash_set_frag3`, `hash_token3`, the `#[global]` instance fields `hash_tape_timeless`,
  `hash_auth_timeless`, `hash_frag_timeless`, `hash_set_timeless`, `hash_set_frag_timeless`,
  `hash_token_timeless`, `con_hash_inv_persistent`, `hash_frag_persistent` (re-exported as
  global instances `con_hash3_*`), and `hash_auth_exclusive`, `hash_auth_frag_agree`,
  `hash_auth_duplicate`, `hash_auth_coll_free`, `hash_frag_frag_agree`, `hash_auth_insert`,
  `hash_tape_valid`, `hash_tape_exclusive`, `hash_token_split`, `hash_tape_presample`,
  `con_hash_init3`, `con_hash_alloc_tape3`, `con_hash_spec3`.
  - The instance argument `{HR : ∀ m, Timeless (R m)}` is `[HR : ∀ m, Timeless (R m)]`.
  - `P -∗ Q` fields are stated as `⊢ P -∗ Q` (or `⊢ P ==∗ Q`); `P ⊣⊢ Q` is `P ⊣⊢ Q`.
  - `Forall (λ x, x <= val_size) ns` is `∀ x ∈ ns, x ≤ val_size`.
  - `gmap nat nat` is `hmap`, `m !! v` is `m[v]?`, `<[v:=n]> m` is `m.insert v n`.
  - Texan triples are iris-lean's (mask `⊤`); `f #v α` is `cpl(&f #v &α)`.
* Section `test`: `hash_tape3'`, `con_hash_spec_test3`, `con_hash_spec_hashed_before3` (same
  names), over `[c : con_hash3 GF val_size max_hash_size max_hash_size_pos]` (Rocq's section
  `Variables`/`Hypothesis` are implicit arguments).

## Omitted
* The commented-out Rocq field `concrete_seq_hash`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Coneris
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map)

namespace Coneris.Examples.HashDir.ConHashInterface3

/-- Rocq: `coll_free`. -/
def coll_free (m : hmap) : Prop :=
  ∀ k1 k2, (m[k1]?).isSome → (m[k2]?).isSome → m.getD k1 0 = m.getD k2 0 → k1 = k2

/-- Rocq: `amortized_error` (a `Program Definition`). -/
def amortized_error (val_size max_hash_size : ℕ) (_H : 0 < max_hash_size) : ℝ≥0∞ :=
  ((max_hash_size : ℝ≥0∞) - 1) / (2 * ((val_size : ℝ≥0∞) + 1))

/-- Rocq: `con_hash3`. -/
class con_hash3 (GF : BundledGFunctors) [conerisGS GF] (val_size max_hash_size : ℕ)
    (Hpos : 0 < max_hash_size) where
  -- * Operations
  init_hash3 : val
  allocate_tape3 : val
  compute_hash3 : val
  -- * Ghost state
  hash_view_gname : Type
  hash_set_gname : Type
  hash_tape_gname : Type
  hash_lock_gname : Type
  hash_view_gname' : Type
  hash_set_gname' : Type
  hash_token_gname : Type
  -- * Predicates
  con_hash_inv3 (N : Namespace) (f l hm : val) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)]
    (γ1 : hash_view_gname) (γ2 : hash_set_gname) (γ3 : hash_tape_gname)
    (γ4 : hash_view_gname') (γ5 : hash_set_gname') (γ6 : hash_token_gname)
    (γ_lock : hash_lock_gname) : IProp GF
  hash_tape3 (α : val) (ns : List ℕ) (γ2 : hash_set_gname) (γ3 : hash_tape_gname) : IProp GF
  hash_auth3 (m : hmap) (γ : hash_view_gname) (γ2 : hash_set_gname) (γ4 : hash_view_gname')
    (γ5 : hash_set_gname') : IProp GF
  hash_frag3 (v res : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname) (γ4 : hash_view_gname') :
    IProp GF
  hash_set3 (s : ℕ) (γ2 : hash_set_gname) (γ5 : hash_set_gname') (γ6 : hash_token_gname) :
    IProp GF
  hash_set_frag3 (n : ℕ) (γ2 : hash_set_gname) (γ5 : hash_set_gname') : IProp GF
  hash_token3 (n : ℕ) (γ6 : hash_token_gname) : IProp GF
  -- * General properties of the predicates
  hash_tape_timeless (α : val) (ns : List ℕ) (γ2 : hash_set_gname) (γ3 : hash_tape_gname) :
    Timeless (hash_tape3 α ns γ2 γ3)
  hash_auth_timeless (m : hmap) (γ : hash_view_gname) (γ2 : hash_set_gname)
    (γ4 : hash_view_gname') (γ5 : hash_set_gname') : Timeless (hash_auth3 m γ γ2 γ4 γ5)
  hash_frag_timeless (v res : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname)
    (γ4 : hash_view_gname') : Timeless (hash_frag3 v res γ γ2 γ4)
  hash_set_timeless (s : ℕ) (γ2 : hash_set_gname) (γ5 : hash_set_gname') (γ6 : hash_token_gname) :
    Timeless (hash_set3 s γ2 γ5 γ6)
  hash_set_frag_timeless (s : ℕ) (γ2 : hash_set_gname) (γ5 : hash_set_gname') :
    Timeless (hash_set_frag3 s γ2 γ5)
  hash_token_timeless (s : ℕ) (γ6 : hash_token_gname) : Timeless (hash_token3 s γ6)
  con_hash_inv_persistent (N : Namespace) (f l hm : val) (γ1 : hash_view_gname)
    (γ2 : hash_set_gname) (γ3 : hash_tape_gname) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ4 : hash_view_gname') (γ5 : hash_set_gname')
    (γ6 : hash_token_gname) (γ_lock : hash_lock_gname) :
    Persistent (con_hash_inv3 N f l hm R γ1 γ2 γ3 γ4 γ5 γ6 γ_lock)
  hash_frag_persistent (v res : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname)
    (γ4 : hash_view_gname') : Persistent (hash_frag3 v res γ γ2 γ4)
  hash_auth_exclusive (m m' : hmap) (γ : hash_view_gname) (γ2 : hash_set_gname)
    (γ4 : hash_view_gname') (γ5 : hash_set_gname') :
    ⊢ hash_auth3 m γ γ2 γ4 γ5 -∗ hash_auth3 m' γ γ2 γ4 γ5 -∗ False
  hash_auth_frag_agree (m : hmap) (k v : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname)
    (γ4 : hash_view_gname') (γ5 : hash_set_gname') :
    ⊢ hash_auth3 m γ γ2 γ4 γ5 -∗ hash_frag3 k v γ γ2 γ4 -∗ ⌜m[k]? = some v⌝
  hash_auth_duplicate (m : hmap) (k v : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname)
    (γ4 : hash_view_gname') (γ5 : hash_set_gname') :
    m[k]? = some v → ⊢ hash_auth3 m γ γ2 γ4 γ5 -∗ hash_frag3 k v γ γ2 γ4
  hash_auth_coll_free (m : hmap) (γ : hash_view_gname) (γ2 : hash_set_gname)
    (γ4 : hash_view_gname') (γ5 : hash_set_gname') :
    ⊢ hash_auth3 m γ γ2 γ4 γ5 -∗ ⌜coll_free m⌝
  hash_frag_frag_agree (k1 k2 v1 v2 : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname)
    (γ4 : hash_view_gname') :
    ⊢ hash_frag3 k1 v1 γ γ2 γ4 -∗ hash_frag3 k2 v2 γ γ2 γ4 -∗ ⌜k1 = k2 ↔ v1 = v2⌝
  hash_auth_insert (m : hmap) (k v : ℕ) (γ1 : hash_view_gname) (γ2 : hash_set_gname)
    (γ4 : hash_view_gname') (γ5 : hash_set_gname') :
    m[k]? = none →
    ⊢ hash_set_frag3 v γ2 γ5 -∗ hash_auth3 m γ1 γ2 γ4 γ5 ==∗ hash_auth3 (m.insert k v) γ1 γ2 γ4 γ5
  hash_tape_valid (α : val) (ns : List ℕ) (γ2 : hash_set_gname) (γ3 : hash_tape_gname) :
    ⊢ hash_tape3 α ns γ2 γ3 -∗ ⌜∀ x ∈ ns, x ≤ val_size⌝
  hash_tape_exclusive (α : val) (ns ns' : List ℕ) (γ2 : hash_set_gname) (γ3 : hash_tape_gname) :
    ⊢ hash_tape3 α ns γ2 γ3 -∗ hash_tape3 α ns' γ2 γ3 -∗ False
  hash_token_split (n n' : ℕ) (γ6 : hash_token_gname) :
    hash_token3 (n + n') γ6 ⊣⊢ hash_token3 n γ6 ∗ hash_token3 n' γ6
  hash_tape_presample (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_hv : hash_view_gname) (γ_set : hash_set_gname)
    (γ_hv' : hash_view_gname') (γ_token : hash_token_gname) (γ : hash_tape_gname)
    (γ_set' : hash_set_gname') (γ_lock : hash_lock_gname) (α : val) (ns : List ℕ) (E : CoPset) :
    ↑N ⊆ E →
    ⊢ con_hash_inv3 N f l hm R γ_hv γ_set γ γ_hv' γ_set' γ_token γ_lock -∗
      hash_tape3 α ns γ_set γ -∗
      ↯ (amortized_error val_size max_hash_size Hpos) -∗
      hash_token3 1 γ_token -∗
      state_update E E iprop(∃ n : Fin (val_size + 1),
        hash_tape3 α (ns ++ [(n : ℕ)]) γ_set γ ∗ hash_set_frag3 (n : ℕ) γ_set γ_set')
  con_hash_init3 (N : Namespace) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] :
    {{ R ∅ }} cpl(&init_hash3 #())
    {{ (f : val), RET f; ∃ l hm γ1 γ2 γ3 γ4 γ5 γ_token γ_lock,
        con_hash_inv3 N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock ∗
        hash_token3 max_hash_size γ_token }}
  con_hash_alloc_tape3 (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash_view_gname) (γ2 : hash_set_gname)
    (γ3 : hash_tape_gname) (γ4 : hash_view_gname') (γ5 : hash_set_gname')
    (γ_token : hash_token_gname) (γ_lock : hash_lock_gname) :
    {{ con_hash_inv3 N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock }} cpl(&allocate_tape3 #())
    {{ (α : val), RET α; hash_tape3 α [] γ2 γ3 }}
  con_hash_spec3 (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash_view_gname) (γ2 : hash_set_gname)
    (γ3 : hash_tape_gname) (γ4 : hash_view_gname') (γ5 : hash_set_gname')
    (γ_token : hash_token_gname) (γ_lock : hash_lock_gname) (Q1 : ℕ → IProp GF)
    (Q2 : ℕ → List ℕ → IProp GF) (α : val) (v : ℕ) :
    {{ con_hash_inv3 N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock ∗
        (∀ m, R m -∗ hash_auth3 m γ1 γ2 γ4 γ5 -∗ state_update ⊤ ⊤
          (match m[v]? with
           | some res => iprop(R m ∗ hash_auth3 m γ1 γ2 γ4 γ5 ∗ Q1 res)
           | none => iprop(∃ n ns, hash_tape3 α (n :: ns) γ2 γ3 ∗
                (hash_tape3 α ns γ2 γ3 ={⊤}=∗ R (m.insert v n) ∗
                  hash_auth3 (m.insert v n) γ1 γ2 γ4 γ5 ∗ Q2 n ns)))) }}
      cpl(&f #v &α)
    {{ (res : ℕ), RET LitV (LitInt (res : ℤ)); Q1 res ∨ ∃ ns, Q2 res ns }}

section instances

variable {GF : BundledGFunctors} [conerisGS GF] {val_size max_hash_size : ℕ}
  {Hpos : 0 < max_hash_size} [c : con_hash3 GF val_size max_hash_size Hpos]

instance con_hash3_hash_tape_timeless (α : val) (ns : List ℕ) (γ2 : c.hash_set_gname)
    (γ3 : c.hash_tape_gname) : Timeless (c.hash_tape3 α ns γ2 γ3) :=
  c.hash_tape_timeless α ns γ2 γ3
instance con_hash3_hash_auth_timeless (m : hmap) (γ : c.hash_view_gname) (γ2 : c.hash_set_gname)
    (γ4 : c.hash_view_gname') (γ5 : c.hash_set_gname') : Timeless (c.hash_auth3 m γ γ2 γ4 γ5) :=
  c.hash_auth_timeless m γ γ2 γ4 γ5
instance con_hash3_hash_frag_timeless (v res : ℕ) (γ : c.hash_view_gname)
    (γ2 : c.hash_set_gname) (γ4 : c.hash_view_gname') : Timeless (c.hash_frag3 v res γ γ2 γ4) :=
  c.hash_frag_timeless v res γ γ2 γ4
instance con_hash3_hash_set_timeless (s : ℕ) (γ2 : c.hash_set_gname) (γ5 : c.hash_set_gname')
    (γ6 : c.hash_token_gname) : Timeless (c.hash_set3 s γ2 γ5 γ6) := c.hash_set_timeless s γ2 γ5 γ6
instance con_hash3_hash_set_frag_timeless (s : ℕ) (γ2 : c.hash_set_gname)
    (γ5 : c.hash_set_gname') : Timeless (c.hash_set_frag3 s γ2 γ5) :=
  c.hash_set_frag_timeless s γ2 γ5
instance con_hash3_hash_token_timeless (s : ℕ) (γ6 : c.hash_token_gname) :
    Timeless (c.hash_token3 s γ6) := c.hash_token_timeless s γ6
instance con_hash3_con_hash_inv_persistent (N : Namespace) (f l hm : val)
    (γ1 : c.hash_view_gname) (γ2 : c.hash_set_gname) (γ3 : c.hash_tape_gname)
    (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] (γ4 : c.hash_view_gname')
    (γ5 : c.hash_set_gname') (γ6 : c.hash_token_gname) (γ_lock : c.hash_lock_gname) :
    Persistent (c.con_hash_inv3 N f l hm R γ1 γ2 γ3 γ4 γ5 γ6 γ_lock) :=
  c.con_hash_inv_persistent N f l hm γ1 γ2 γ3 R γ4 γ5 γ6 γ_lock
instance con_hash3_hash_frag_persistent (v res : ℕ) (γ : c.hash_view_gname)
    (γ2 : c.hash_set_gname) (γ4 : c.hash_view_gname') : Persistent (c.hash_frag3 v res γ γ2 γ4) :=
  c.hash_frag_persistent v res γ γ2 γ4

end instances

section test

variable {val_size max_hash_size : ℕ} {max_hash_size_pos : 0 < max_hash_size}
variable {GF : BundledGFunctors} [conerisGS GF]
  [c : con_hash3 GF val_size max_hash_size max_hash_size_pos]

/-- Rocq: `hash_tape3'`. -/
def hash_tape3' (α : val) (ns : List ℕ) (γ2 : c.hash_set_gname) (γ3 : c.hash_tape_gname)
    (γ5 : c.hash_set_gname') : IProp GF :=
  iprop(c.hash_tape3 α ns γ2 γ3 ∗ [∗list] n ∈ ns, c.hash_set_frag3 n γ2 γ5)

/-- Rocq: `con_hash_spec_test3`. -/
theorem con_hash_spec_test3 (N : Namespace) (f l hm : val) (γ1 : c.hash_view_gname)
    (γ2 : c.hash_set_gname) (γ3 : c.hash_tape_gname) (γ4 : c.hash_view_gname')
    (γ5 : c.hash_set_gname') (γ_token : c.hash_token_gname) (γlock : c.hash_lock_gname) (α : val) (n : ℕ) (ns : List ℕ)
    (v : ℕ) :
    {{ c.con_hash_inv3 N f l hm (fun _ => iprop(True)) γ1 γ2 γ3 γ4 γ5 γ_token γlock ∗
        hash_tape3' α (n :: ns) γ2 γ3 γ5 }}
      cpl(&f #v &α)
    {{ (res : ℕ), RET LitV (LitInt (res : ℤ)); c.hash_frag3 v res γ1 γ2 γ4 ∗
        ((hash_tape3' α ns γ2 γ3 γ5 ∗ ⌜res = n⌝) ∨ hash_tape3' α (n :: ns) γ2 γ3 γ5) }} := by
  unfold hash_tape3'
  iintro %Φ ⟨#Hinv, Ht, Hlis⟩ HΦ
  iapply c.con_hash_spec3 N f l hm (fun _ => iprop(True)) γ1 γ2 γ3 γ4 γ5 γ_token γlock
    (fun res => iprop(c.hash_frag3 v res γ1 γ2 γ4 ∗ c.hash_tape3 α (n :: ns) γ2 γ3 ∗
      [∗list] n0 ∈ (n :: ns), c.hash_set_frag3 n0 γ2 γ5))
    (fun n' ns' => iprop(⌜n = n'⌝ ∗ ⌜ns = ns'⌝ ∗ c.hash_frag3 v n γ1 γ2 γ4 ∗
      c.hash_tape3 α ns γ2 γ3 ∗ [∗list] n0 ∈ ns, c.hash_set_frag3 n0 γ2 γ5))
    α v $$ [Ht Hlis]
  · isplitr
    · iexact Hinv
    iintro %m - Hauth
    cases hm' : m[v]? with
    | some res =>
      ihave ⟨Hauth, #Hf⟩ := persistent_entails_left
        (wand_entails (c.hash_auth_duplicate m v res γ1 γ2 γ4 γ5 hm')) $$ Hauth
      dsimp only
      imodintro
      iframe Hauth Hf Ht Hlis
    | none =>
      dsimp only
      ihave ⟨H1, Hlis⟩ := BigSepL.bigSepL_cons.1 $$ Hlis
      imod c.hash_auth_insert m v n γ1 γ2 γ4 γ5 hm' $$ H1 Hauth with H
      ihave ⟨H, #Hf⟩ := persistent_entails_left
        (wand_entails (c.hash_auth_duplicate (m.insert v n) v n γ1 γ2 γ4 γ5 (by simp))) $$ H
      imodintro
      iexists n, ns
      iframe Ht
      iintro Ht
      imodintro
      iframe H Hf Ht Hlis
      isplitr <;> ipureintro <;> rfl
  iintro !> %res H
  icases H with (⟨#Hf, Ht, Hlis⟩ | ⟨%ns', %Hn, %Hns, #Hf, Ht, Hlis⟩)
  · iapply HΦ
    iframe Hf
    iright
    iframe
  · subst Hn Hns
    iapply HΦ
    iframe Hf
    ileft
    iframe Ht Hlis
    ipureintro
    rfl

/-- Rocq: `con_hash_spec_hashed_before3`. -/
theorem con_hash_spec_hashed_before3 (N : Namespace) (f l hm : val) (γ1 : c.hash_view_gname)
    (γ2 : c.hash_set_gname) (γ3 : c.hash_tape_gname) (γ4 : c.hash_view_gname')
    (γ5 : c.hash_set_gname') (γ_token : c.hash_token_gname) (γlock : c.hash_lock_gname) (α : val) (ns : List ℕ) (res v : ℕ) :
    {{ c.con_hash_inv3 N f l hm (fun _ => iprop(True)) γ1 γ2 γ3 γ4 γ5 γ_token γlock ∗
        hash_tape3' α ns γ2 γ3 γ5 ∗ c.hash_frag3 v res γ1 γ2 γ4 }}
      cpl(&f #v &α)
    {{ RET LitV (LitInt (res : ℤ)); c.hash_frag3 v res γ1 γ2 γ4 ∗ hash_tape3' α ns γ2 γ3 γ5 }} := by
  unfold hash_tape3'
  iintro %Φ ⟨#Hinv, ⟨Ht, Hlis⟩, #Hf⟩ HΦ
  iapply c.con_hash_spec3 N f l hm (fun _ => iprop(True)) γ1 γ2 γ3 γ4 γ5 γ_token γlock
    (fun res' => iprop(⌜res = res'⌝ ∗ c.hash_tape3 α ns γ2 γ3 ∗ c.hash_frag3 v res γ1 γ2 γ4))
    (fun _ _ => iprop(⌜False⌝)) α v $$ [Ht]
  · isplitr
    · iexact Hinv
    iintro %m - Hauth
    ihave %Hlk := c.hash_auth_frag_agree m v res γ1 γ2 γ4 γ5 $$ Hauth Hf
    rw [Hlk]
    dsimp only
    imodintro
    iframe Hauth Hf Ht
    ipureintro
    rfl
  iintro !> %res' H
  icases H with (⟨%Heq, Ht, -⟩ | ⟨%_, %Hfalse⟩)
  · subst Heq
    iapply HΦ
    iframe Hf Ht Hlis
  · exact Hfalse.elim

end test

end Coneris.Examples.HashDir.ConHashInterface3
