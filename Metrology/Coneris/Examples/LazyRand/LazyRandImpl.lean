module

public import Metrology.Coneris.Examples.LazyRand.LazyRandInterface
public import Metrology.Coneris.Lib.HocapRandAlt
public import Metrology.Coneris.Lib.Lock
public import Iris.Instances.Lib.GhostMap

/-!
# An implementation of the lazy rand interface

Ported from clutch/theories/coneris/examples/lazy_rand/lazy_rand_impl.v

## Rocq → Lean mapping
* Section `impl`: the section variable `val_size` is explicit; the context
  `Hv: !ghost_mapG Σ () (option (nat*nat))`, `lo:lock`, `Hl: lockG Σ`, `Hr: !rand_spec' val_size`
  is `[Hv : GhostMapG GF Unit (Option (ℕ × ℕ)) unit_map] [lo : lock] (L : lo.lockG GF)
  [Hr : rand_spec' val_size GF]` (as in `Coneris.Lib.Lock`, the lock's ghost-state assumption
  is an explicit argument `L`).
* `gmap () (option (nat*nat))` is `unit_map (Option (ℕ × ℕ))`, with the helper
  `unit_map := (Std.ExtTreeMap Unit · compare)`; `<[():=n]>∅` is iris-lean's
  `Iris.Std.insert ∅ () n`.
* `ghost_map_auth γ 1 m` is `γ ↪●MAP m`, `k ↪[γ] v` is `γ ↪◯MAP[k] v`, `k ↪[γ]□ v` is
  `γ ↪◯MAP[k]{.discard} v`.
* The programs are transcribed with the `cpl` notation; `newlock`, `acquire`, `release`,
  `rand_allocate_tape`, `rand_tape` are the generic `lo.newlock`, ..., `Hr.rand_tape`.
* `option_to_list`, `rand_tape_frag`, `abstract_lazy_rand_inv`, `option_to_gmap`,
  `option_valid`, `option_to_val`, `rand_frag`, `option_duplicate`, `rand_auth`,
  `lazy_rand_inv`, `rand_tape_presample_impl`, `lazy_rand_init_impl`,
  `lazy_rand_alloc_tape_impl`, `lazy_rand_spec_impl`: same names.
* `lazy_rand_impl` (Rocq: `Program Definition`) is a definition (not an instance), taking the
  lock ghost-state argument `L`. Its `Next Obligation`s are the helper theorems
  `lazy_rand_impl_rand_tape_frag_valid`, `lazy_rand_impl_rand_tape_frag_exclusive`,
  `lazy_rand_impl_rand_auth_exclusive`, `lazy_rand_impl_rand_auth_frag_agree`,
  `lazy_rand_impl_rand_auth_duplicate`, `lazy_rand_impl_rand_auth_valid`,
  `lazy_rand_impl_rand_frag_valid`, `lazy_rand_impl_rand_frag_frag_agree`,
  `lazy_rand_impl_rand_auth_update`; the timeless/persistent obligations (solved automatically
  in Rocq) are the instances `rand_tape_frag_timeless`, `rand_auth_timeless`, etc.

## Added
* `unit_lawfulEqCmp`, `unit_map` (helpers for Unit-keyed ghost maps).
* In `lazy_rand_inv`, the unused Rocq argument `{HP : ∀ n, Timeless (P n)}` is `[_HP : ...]`.

## Omitted
* The commented-out Rocq code (`abstract_tapes` reasoning, `rand_tape_auth`,
  `lazy_rand_presample_impl`, the commented-out `Next Obligation`s).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Lock Coneris.Lib.HocapRandAlt
open Coneris.Examples.LazyRand.LazyRandInterface

namespace Coneris.Examples.LazyRand.LazyRandImpl

/-- Helper: `compare` on `Unit` is lawful (needed to key `Std.ExtTreeMap`s by `Unit`). -/
instance unit_lawfulEqCmp : Std.LawfulEqCmp (compare : Unit → Unit → Ordering) where
  eq_of_compare _ := rfl
  compare_self := compare_eq_iff_eq.2 rfl

/-- Helper: finite maps keyed by `Unit` (Rocq: `gmap ()`). -/
abbrev unit_map : Type → Type := (Std.ExtTreeMap Unit · compare)

section impl

variable (val_size : ℕ)
variable {GF : BundledGFunctors} [Hc : conerisGS GF]
  [Hv : GhostMapG GF Unit (Option (ℕ × ℕ)) unit_map] [lo : lock] (L : lo.lockG GF)
  [Hr : rand_spec' val_size GF]

/-- Rocq: `init_lazy_rand_prog`. -/
def init_lazy_rand_prog : val := cpl_val(
  λ _, let x := ref(none()) in
    let l := v(&lo.newlock) #() in
    (l, x))

/-- Rocq: `allocate_tape_prog`. -/
def allocate_tape_prog : val := cpl_val(λ _, v(&Hr.rand_allocate_tape) #())

/-- Rocq: `lazy_read_rand_prog`. -/
def lazy_read_rand_prog : val := cpl_val(
  λ r α tid,
    let (l, x) := r;
    v(&lo.acquire) l;
    let val := (match !x with
                | some(x') => x'
                | none() =>
                    let x' := (v(&Hr.rand_tape) α, tid) in
                    x ← some(x');
                    x') in
    v(&lo.release) l;
    val)

/-- Rocq: `option_to_list`. -/
def option_to_list (n : Option ℕ) : List ℕ :=
  match n with
  | some n' => [n']
  | none => []

/-- Rocq: `rand_tape_frag`. -/
def rand_tape_frag (α : val) (n : Option ℕ) (γ : Hr.rand_tape_name) : IProp GF :=
  Hr.rand_tapes α (option_to_list n) γ

/-- Rocq: `abstract_lazy_rand_inv`. -/
def abstract_lazy_rand_inv (N : Namespace) (γ_tape : Hr.rand_tape_name) : IProp GF :=
  Hr.is_rand N γ_tape

/-- Rocq: `option_to_gmap`. -/
def option_to_gmap (n : Option (ℕ × ℕ)) : unit_map (Option (ℕ × ℕ)) :=
  Iris.Std.insert (∅ : unit_map (Option (ℕ × ℕ))) () n

/-- Rocq: `option_valid`. -/
def option_valid (n : Option (ℕ × ℕ)) : Prop :=
  match n with
  | some (n1, _) => n1 ≤ val_size
  | none => True

/-- Rocq: `option_to_val`. -/
def option_to_val (n : Option (ℕ × ℕ)) : val :=
  match n with
  | some (n1, n2) => cpl_val(some((#n1, #n2)))
  | none => cpl_val(none())

/-- Rocq: `rand_frag`. -/
def rand_frag (res tid : ℕ) (γ : GName) : IProp GF :=
  iprop((γ ↪◯MAP[()]{.discard} (some (res, tid))) ∗ ⌜res ≤ val_size⌝)

/-- Rocq: `option_duplicate`. -/
def option_duplicate (n : Option (ℕ × ℕ)) (γ : GName) : IProp GF :=
  match n with
  | some (n1, n2) => rand_frag val_size n1 n2 γ
  | none => iprop(γ ↪◯MAP[()] (none : Option (ℕ × ℕ)))

/-- Rocq: `rand_auth`. -/
def rand_auth (n : Option (ℕ × ℕ)) (γ : GName) : IProp GF :=
  iprop((γ ↪●MAP option_to_gmap n) ∗ option_duplicate val_size n γ ∗ ⌜option_valid val_size n⌝)

/-- Rocq: `lazy_rand_inv`. -/
def lazy_rand_inv (N : Namespace) (c : val) (P : Option (ℕ × ℕ) → IProp GF)
    [_HP : ∀ n, Timeless (P n)] (γ_tape : Hr.rand_tape_name) (γ_view : GName)
    (γ_lock : lo.lock_name) : IProp GF :=
  iprop(∃ (lk : val) (l : Loc),
    ⌜c = PairV lk (LitV (LitLoc l))⌝ ∗
    abstract_lazy_rand_inv val_size N γ_tape ∗
    lo.is_lock L γ_lock lk
      iprop(∃ res, P res ∗ rand_auth val_size res γ_view ∗ l ↦ option_to_val res))

/-! ### Timelessness / persistence (the automatic obligations) -/

instance rand_tape_frag_timeless (α : val) (n : Option ℕ) (γ : Hr.rand_tape_name) :
    Timeless (rand_tape_frag val_size α n γ) := by
  unfold rand_tape_frag; infer_instance

instance rand_frag_timeless (res tid : ℕ) (γ : GName) :
    Timeless (rand_frag (GF := GF) val_size res tid γ) := by
  unfold rand_frag; infer_instance

instance rand_frag_persistent (res tid : ℕ) (γ : GName) :
    Persistent (rand_frag (GF := GF) val_size res tid γ) := by
  unfold rand_frag; infer_instance

instance option_duplicate_timeless (n : Option (ℕ × ℕ)) (γ : GName) :
    Timeless (option_duplicate (GF := GF) val_size n γ) := by
  rcases n with _ | ⟨n1, n2⟩ <;> unfold option_duplicate <;> infer_instance

instance rand_auth_timeless (n : Option (ℕ × ℕ)) (γ : GName) :
    Timeless (rand_auth (GF := GF) val_size n γ) := by
  unfold rand_auth; infer_instance

instance lazy_rand_inv_persistent (N : Namespace) (c : val) (P : Option (ℕ × ℕ) → IProp GF)
    [HP : ∀ n, Timeless (P n)] (γ_tape : Hr.rand_tape_name) (γ_view : GName)
    (γ_lock : lo.lock_name) :
    Persistent (lazy_rand_inv val_size L N c P γ_tape γ_view γ_lock) := by
  unfold lazy_rand_inv abstract_lazy_rand_inv; infer_instance

/-! ### The `Next Obligation`s of `lazy_rand_impl` -/

/-- Rocq: first `Next Obligation` of `lazy_rand_impl` (`rand_tape_frag_valid`). -/
theorem lazy_rand_impl_rand_tape_frag_valid (α : val) (ns : ℕ) (γ : Hr.rand_tape_name) :
    ⊢ rand_tape_frag val_size α (some ns) γ -∗ ⌜ns ≤ val_size⌝ := by
  unfold rand_tape_frag
  iintro H
  ihave %H := Hr.rand_tapes_valid α _ γ $$ H
  ipureintro
  exact H ns (List.mem_singleton_self ns)

/-- Rocq: second `Next Obligation` of `lazy_rand_impl` (`rand_tape_frag_exclusive`). -/
theorem lazy_rand_impl_rand_tape_frag_exclusive (α : val) (ns ns' : Option ℕ)
    (γ : Hr.rand_tape_name) :
    ⊢ rand_tape_frag val_size α ns γ -∗ rand_tape_frag val_size α ns' γ -∗ False := by
  unfold rand_tape_frag
  iintro H1 H2
  iapply Hr.rand_tapes_exclusive $$ H1 H2

/-- Rocq: third `Next Obligation` of `lazy_rand_impl` (`rand_auth_exclusive`). -/
theorem lazy_rand_impl_rand_auth_exclusive (n n' : Option (ℕ × ℕ)) (γ : GName) :
    ⊢@{IProp GF} rand_auth val_size n γ -∗ rand_auth val_size n' γ -∗ False := by
  unfold rand_auth
  iintro ⟨H1, -⟩ ⟨H2, -⟩
  ihave %H := ghost_map_auth_valid_2 $$ H1 H2
  exact absurd (DFrac.valid_own_op H.1) (by simp)

/-- Rocq: fourth `Next Obligation` of `lazy_rand_impl` (`rand_auth_frag_agree`). -/
theorem lazy_rand_impl_rand_auth_frag_agree (n : Option (ℕ × ℕ)) (n' tid : ℕ) (γ : GName) :
    ⊢@{IProp GF} rand_auth val_size n γ -∗ rand_frag val_size n' tid γ -∗
      ⌜n = some (n', tid)⌝ := by
  unfold rand_auth rand_frag
  iintro ⟨H, -⟩ ⟨H', -⟩
  ihave %H := ghost_map_lookup $$ H H'
  ipureintro
  unfold option_to_gmap at H
  rw [get?_insert_eq rfl] at H
  exact Option.some.inj H

/-- Rocq: fifth `Next Obligation` of `lazy_rand_impl` (`rand_auth_duplicate`). -/
theorem lazy_rand_impl_rand_auth_duplicate (n : ℕ × ℕ) (γ : GName) :
    ⊢@{IProp GF} rand_auth val_size (some n) γ -∗ rand_frag val_size n.1 n.2 γ := by
  obtain ⟨n1, n2⟩ := n
  unfold rand_auth option_duplicate
  iintro ⟨-, H, -⟩
  iexact H

/-- Rocq: sixth `Next Obligation` of `lazy_rand_impl` (`rand_auth_valid`). -/
theorem lazy_rand_impl_rand_auth_valid (n tid : ℕ) (γ : GName) :
    ⊢@{IProp GF} rand_auth val_size (some (n, tid)) γ -∗ ⌜n ≤ val_size⌝ := by
  unfold rand_auth
  iintro ⟨-, -, %H⟩
  ipureintro
  exact H

/-- Rocq: seventh `Next Obligation` of `lazy_rand_impl` (`rand_frag_valid`). -/
theorem lazy_rand_impl_rand_frag_valid (n tid : ℕ) (γ : GName) :
    ⊢@{IProp GF} rand_frag val_size n tid γ -∗ ⌜n ≤ val_size⌝ := by
  unfold rand_frag
  iintro ⟨-, %H⟩
  ipureintro
  exact H

/-- Rocq: eighth `Next Obligation` of `lazy_rand_impl` (`rand_frag_frag_agree`). -/
theorem lazy_rand_impl_rand_frag_frag_agree (v1 v2 tid1 tid2 : ℕ) (γ : GName) :
    ⊢@{IProp GF} rand_frag val_size v1 tid1 γ -∗ rand_frag val_size v2 tid2 γ -∗
      ⌜v1 = v2 ∧ tid1 = tid2⌝ := by
  unfold rand_frag
  iintro ⟨H, -⟩ ⟨H', -⟩
  ihave %H := ghost_map_elem_agree $$ [H H']
  · iframe
  ipureintro
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  exact ⟨H.1.symm, H.2.symm⟩

/-- Rocq: ninth `Next Obligation` of `lazy_rand_impl` (`rand_auth_update`). -/
theorem lazy_rand_impl_rand_auth_update (n : ℕ × ℕ) (γ : GName) (Hn : n.1 ≤ val_size) :
    ⊢@{IProp GF} rand_auth val_size none γ ==∗ rand_auth val_size (some n) γ := by
  obtain ⟨n1, n2⟩ := n
  unfold rand_auth
  iintro ⟨H1, H2, -⟩
  unfold option_duplicate
  imod ghost_map_update (some (n1, n2)) $$ H1 H2 with ⟨H1, H2⟩
  unfold option_to_gmap
  rw [LawfulPartialMap.insert_insert_same]
  imod ghost_map_elem_persist $$ H2 with H2
  imodintro
  iframe H1
  simp only [rand_frag, option_valid]
  iframe H2
  ipureintro
  exact ⟨Hn, Hn⟩

/-! ### The specs -/

/-- Rocq: `rand_tape_presample_impl`. -/
theorem rand_tape_presample_impl (N : Namespace) (c : val) (P : Option (ℕ × ℕ) → IProp GF)
    [HP : ∀ n, Timeless (P n)] (γ : Hr.rand_tape_name) (γ_view : GName)
    (γ_lock : lo.lock_name) (E : CoPset) (α : val) (ε : ℝ≥0∞)
    (ε2 : Fin (val_size + 1) → ℝ≥0∞) (HN : ↑N ⊆ E)
    (Hsum : ∑' n, 1 / ((val_size : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢ lazy_rand_inv val_size L N c P γ γ_view γ_lock -∗
      rand_tape_frag val_size α none γ -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (val_size + 1),
        ↯ (ε2 n) ∗ rand_tape_frag val_size α (some (n : ℕ)) γ) := by
  unfold lazy_rand_inv abstract_lazy_rand_inv rand_tape_frag option_to_list
  iintro ⟨%lk, %l, %Hc, #Hinv, #Hlock⟩ Htape Herr
  imod Hr.rand_tapes_presample N E α [] ε ε2 γ HN Hsum $$ Hinv Htape Herr with ⟨%n, Herr, Htape⟩
  simp only [List.nil_append]
  imodintro
  iexists n
  iframe Herr
  iexact Htape

/-- Rocq: `lazy_rand_init_impl`. -/
theorem lazy_rand_init_impl (N : Namespace) (P : Option (ℕ × ℕ) → IProp GF)
    [HP : ∀ n, Timeless (P n)] :
    {{ P none }} cpl(v(&init_lazy_rand_prog) #())
    {{ c, RET c; ∃ γ γ_view γ_lock, lazy_rand_inv val_size L N c P γ γ_view γ_lock }} := by
  iintro %Φ HP HΦ
  iapply pgl_wp_fupd
  unfold init_lazy_rand_prog
  wp_pures
  wp_alloc x as Hx
  wp_pures
  imod ghost_map_alloc (GF := GF) (H := unit_map) (option_to_gmap none) with ⟨%γ_view, Hm, Ht⟩
  wp_apply lo.newlock_spec L
    iprop(∃ res, P res ∗ rand_auth val_size res γ_view ∗ x ↦ option_to_val res) $$ [HP Hx Hm Ht]
    with %lk %γ_lock #Hlock
  · iexists none
    unfold rand_auth option_duplicate option_valid option_to_val
    iframe HP Hx Hm
    isplitl
    · iapply (BigSepM.bigSepM_lookup (M := unit_map) (m := option_to_gmap none) (i := ())
        (x := none) (Φ := fun k v => iprop(γ_view ↪◯MAP[k] v))
        (by unfold option_to_gmap; exact get?_insert_eq rfl)) $$ Ht
    · ipureintro; trivial
  wp_pures
  imod Hr.rand_inv_create_spec N ⊤ CoPset.subseteq_top with ⟨%γ, #Hrand⟩
  imodintro
  iapply HΦ
  unfold lazy_rand_inv abstract_lazy_rand_inv
  iexists γ, γ_view, γ_lock, lk, x
  iframe Hrand Hlock
  ipureintro
  rfl

/-- Rocq: `lazy_rand_alloc_tape_impl`. -/
theorem lazy_rand_alloc_tape_impl (N : Namespace) (c : val) (P : Option (ℕ × ℕ) → IProp GF)
    [HP : ∀ n, Timeless (P n)] (γ_tape : Hr.rand_tape_name) (γ_view : GName)
    (γ_lock : lo.lock_name) :
    {{ lazy_rand_inv val_size L N c P γ_tape γ_view γ_lock }}
      cpl(v(&(allocate_tape_prog val_size)) #())
    {{ α, RET α; rand_tape_frag val_size α none γ_tape }} := by
  unfold lazy_rand_inv abstract_lazy_rand_inv
  iintro %Φ ⟨%lk, %l, %Hc, #Hinv, -⟩ HΦ
  unfold allocate_tape_prog
  wp_pures
  iapply pgl_wp_fupd
  wp_apply Hr.rand_allocate_tape_spec N γ_tape ⊤ CoPset.subseteq_top $$ Hinv
    with %α ⟨Htoken, Hrand⟩
  iapply HΦ
  unfold rand_tape_frag option_to_list
  imodintro
  iexact Hrand

/-- Rocq: `lazy_rand_spec_impl`. -/
theorem lazy_rand_spec_impl (N : Namespace) (c : val) (P : Option (ℕ × ℕ) → IProp GF)
    [HP : ∀ n, Timeless (P n)] (γ_tape : Hr.rand_tape_name) (γ_view : GName)
    (γ_lock : lo.lock_name) (Q1 Q2 : ℕ → ℕ → IProp GF) (α : val) (tid : ℕ) :
    {{ lazy_rand_inv val_size L N c P γ_tape γ_view γ_lock ∗
        (∀ n, P n -∗ rand_auth val_size n γ_view -∗ state_update ⊤ ⊤
          (match n with
           | some (res, tid') => iprop(P n ∗ rand_auth val_size n γ_view ∗ Q1 res tid')
           | none => iprop(∃ n', rand_tape_frag val_size α (some n') γ_tape ∗
                (rand_tape_frag val_size α none γ_tape ={⊤}=∗
                  P (some (n', tid)) ∗ rand_auth val_size (some (n', tid)) γ_view ∗
                    Q2 n' tid)))) }}
      cpl(v(&(lazy_read_rand_prog val_size)) v(&c) v(&α) #tid)
    {{ (res' tid' : ℕ), RET cpl_val((#res', #tid')); Q1 res' tid' ∨ Q2 res' tid' }} := by
  unfold lazy_rand_inv abstract_lazy_rand_inv
  iintro %Φ ⟨⟨%lk, %l, %Hc, #Hinv, #Hlock⟩, Hvs⟩ HΦ
  subst Hc
  unfold lazy_read_rand_prog
  wp_pures
  wp_apply lo.acquire_spec L γ_lock lk _ $$ Hlock with ⟨Hl, %res, HP, Hauth, Hloc⟩
  wp_pures
  wp_load
  iapply state_update_pgl_wp
  imod Hvs $$ HP Hauth with Hcont
  rcases res with _ | ⟨r, t⟩
  · icases Hcont with ⟨%n', Ht, Hvs⟩
    imodintro
    unfold option_to_val
    wp_pures
    unfold rand_tape_frag option_to_list
    wp_apply Hr.rand_tape_spec_some N γ_tape ⊤ α n' [] CoPset.subseteq_top $$ [Ht] with Htape
    · iframe Hinv Ht
    iapply fupd_pgl_wp
    imod Hvs $$ Htape with ⟨HP, Hrand, HQ⟩
    imodintro
    wp_pures
    wp_store
    wp_pures
    wp_apply lo.release_spec L γ_lock lk _ $$ [Hl HP Hloc Hrand] with -
    · iframe Hlock Hl
      iexists some (n', tid)
      iframe
    wp_pures
    imodintro
    iapply HΦ
    iright
    iexact HQ
  · icases Hcont with ⟨HP, Hauth, HQ⟩
    imodintro
    unfold option_to_val
    wp_pures
    wp_apply lo.release_spec L γ_lock lk _ $$ [Hl HP Hloc Hauth] with -
    · iframe Hlock Hl
      iexists some (r, t)
      iframe
    wp_pures
    iapply HΦ
    ileft
    iexact HQ

/-- Rocq: `lazy_rand_impl` (a `Program Definition`). -/
@[instance_reducible]
def lazy_rand_impl : lazy_rand val_size GF where
  init_lazy_rand := init_lazy_rand_prog
  allocate_tape := allocate_tape_prog val_size
  lazy_read_rand := lazy_read_rand_prog val_size
  rand_tape_gname := Hr.rand_tape_name
  rand_view_gname := GName
  rand_lock_gname := lo.lock_name
  rand_inv N c P _ γ γ_view γ_lock := lazy_rand_inv val_size L N c P γ γ_view γ_lock
  rand_tape_frag := rand_tape_frag val_size
  rand_auth := rand_auth val_size
  rand_frag := rand_frag val_size
  rand_tape_frag_timeless := rand_tape_frag_timeless val_size
  rand_auth_timeless := rand_auth_timeless val_size
  rand_frag_timeless := rand_frag_timeless val_size
  rand_tape_frag_valid := lazy_rand_impl_rand_tape_frag_valid val_size
  rand_inv_persistent N c P _ γ γ_view γ_lock :=
    lazy_rand_inv_persistent val_size L N c P γ γ_view γ_lock
  rand_frag_persistent := rand_frag_persistent val_size
  rand_tape_frag_exclusive := lazy_rand_impl_rand_tape_frag_exclusive val_size
  rand_auth_exclusive := lazy_rand_impl_rand_auth_exclusive val_size
  rand_auth_frag_agree := lazy_rand_impl_rand_auth_frag_agree val_size
  rand_auth_duplicate := lazy_rand_impl_rand_auth_duplicate val_size
  rand_auth_valid := lazy_rand_impl_rand_auth_valid val_size
  rand_frag_valid := lazy_rand_impl_rand_frag_valid val_size
  rand_frag_frag_agree := lazy_rand_impl_rand_frag_frag_agree val_size
  rand_auth_update n γ Hn := lazy_rand_impl_rand_auth_update val_size n γ Hn
  rand_tape_presample N c P _ γ γ_view γ_lock E α ε ε2 HN Hsum :=
    rand_tape_presample_impl val_size L N c P γ γ_view γ_lock E α ε ε2 HN Hsum
  lazy_rand_init N P _ := lazy_rand_init_impl val_size L N P
  lazy_rand_alloc_tape N c P _ γ γ_view γ_lock :=
    lazy_rand_alloc_tape_impl val_size L N c P γ γ_view γ_lock
  lazy_rand_spec N c P _ γ γ_view γ_lock Q1 Q2 α tid :=
    lazy_rand_spec_impl val_size L N c P γ γ_view γ_lock Q1 Q2 α tid

end impl

end Coneris.Examples.LazyRand.LazyRandImpl
