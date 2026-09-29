module

public import Metrology.Coneris.Examples.HashDir.ConHashInterface0
public import Metrology.Coneris.Lib.HocapRandAlt
public import Metrology.Coneris.Lib.Map
public import Metrology.Coneris.Lib.Lock

/-!
# A concurrent hash implementation (version 0)

Ported from clutch/theories/coneris/examples/hash/con_hash_impl0.v

## Rocq → Lean mapping
* Section `con_hash_impl`: the section variable `val_size` is explicit; the context
  `Hc: conerisGS Σ, lo:lock, Hl: lockG Σ, Hr: !rand_spec' val_size` is
  `[conerisGS GF] [lo : lock] (L : lo.lockG GF) [Hr : rand_spec' val_size GF]` (as in
  `Coneris.Lib.Lock`, the lock's ghost-state assumption is an explicit argument `L`).
* Programs (same names): `init_hash_state`, `compute_hash`, `compute_con_hash`, `init_hash`,
  `allocate_tape`, `compute_con_hash_specialized`, transcribed with the `cpl` notation.
  `rand_tape`/`rand_allocate_tape` are the `rand_spec'` operations `Hr.rand_tape`,
  `Hr.rand_allocate_tape`; `acquire`/`release`/`newlock` the lock operations `lo.acquire`, etc.;
  `get`/`set`/`init_map` those of `Coneris.Lib.Map`. Rocq's binder `"_"` is the named binder
  `"_"`; `let, ("l", "hm") := "lhm" in e` is `let (l, hm) := lhm; e`.
* Predicates (same names): `hash_tape`, `abstract_con_hash`, `abstract_con_hash_inv`,
  `concrete_con_hash`, `concrete_con_hash_inv`, `con_hash_inv`. The instance argument
  `{HR : ∀ m, Timeless (R m)}` is `[HR : ∀ m, Timeless (R m)]`.
  - `gmap nat nat` is `hmap`, `(λ b, LitV (LitInt (Z.of_nat b))) <$> m` is
    `m.map (fun _ b => LitV (LitInt (b : ℤ)))`; `m !! v` is `m[v]?`, `<[v:=n]> m` is
    `m.insert v n`.
* Lemmas (same names): `con_hash_tape_presample`, `con_hash_init`, `con_hash_alloc_tape`,
  `con_hash_spec`. Errors are `ℝ≥0∞` (the hypothesis `∀ x, 0 <= ε2 x` is dropped, as in
  `ConHashInterface0`).
* `Program Definition con_hash_impl0 : con_hash0 val_size` is the definition `con_hash_impl0`
  (not an instance, as in Rocq), taking `L` explicitly. Its two `Next Obligation`s are the
  lemmas `con_hash_impl0_hash_tape_valid` and `con_hash_impl0_hash_tape_exclusive`; the
  timeless/persistent obligations (solved automatically in Rocq) are the instances
  `hash_tape_timeless`, `con_hash_inv_persistent`.

## Added
* `hmap_map_insert`, `hmap_map_empty` (stdpp's `fmap_insert`, `fmap_empty` for the value map).

## Omitted
* The commented-out proof fragments in `con_hash_tape_presample` and `con_hash_spec`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Lock Coneris.Lib.HocapRandAlt Coneris.Lib.Map
open Coneris.Examples.HashDir.ConHashInterface0
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map)

namespace Coneris.Examples.HashDir.ConHashImpl0

/-- Helper (stdpp: `fmap_insert`), for the value map of `concrete_con_hash`. -/
theorem hmap_map_insert (m : hmap) (n x : ℕ) :
    (m.insert n x).map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ))) =
      (m.map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ)))).insert n (LitV (LitInt (x : ℤ))) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_map]
  split <;> simp

/-- Helper (stdpp: `fmap_empty`), for the value map of `concrete_con_hash`. -/
theorem hmap_map_empty :
    (∅ : hmap).map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ))) = ∅ :=
  Std.ExtTreeMap.ext_getElem? fun k => by
    rw [Std.ExtTreeMap.getElem?_map]
    simp

section con_hash_impl

variable (val_size : ℕ)
variable {GF : BundledGFunctors} [Hc : conerisGS GF] [lo : lock] (L : lo.lockG GF)
  [Hr : rand_spec' val_size GF]

/-! ## Programs -/

/-- Rocq: `init_hash_state`. A hash function's internal state is a map from previously queried
keys to their hash value. -/
def init_hash_state : val := init_map

/-- Rocq: `compute_hash`. To hash a value `v`, we check whether it is in the map (i.e. it has
been previously hashed). If it has we return the saved hash value, otherwise we draw a hash
value and save it in the map. -/
def compute_hash : val :=
  cpl_val(λ hm v α,
    match &get hm v with
    | some(b) => b
    | none() =>
        let b := &(Hr.rand_tape) α in
        &set hm v b;
        b)

/-- Rocq: `compute_con_hash`. -/
def compute_con_hash : val :=
  cpl_val(λ lhm v α,
    let (l, hm) := lhm;
    &lo.acquire l;
    let output := &(compute_hash val_size) hm v α in
    &lo.release l;
    output)

/-- Rocq: `init_hash`. `init_hash` returns a hash as a function, basically wrapping the
internal state in the returned function. -/
def init_hash : val :=
  cpl_val(λ "_",
    let hm := &init_hash_state #() in
    let l := &lo.newlock #() in
    &(compute_con_hash val_size) (l, hm))

/-- Rocq: `allocate_tape`. -/
def allocate_tape : val :=
  cpl_val(λ "_", &(Hr.rand_allocate_tape) #())

/-- Rocq: `compute_con_hash_specialized`. -/
def compute_con_hash_specialized (lhm : val) : val :=
  cpl_val(λ v α,
    let (l, hm) := &lhm;
    &lo.acquire l;
    let output := (&(compute_hash val_size) hm) v α in
    &lo.release l;
    output)

/-- Sanity check: the transcription of `compute_hash` is the intended AST. -/
example : compute_hash val_size =
    val.RecV .BAnon (.BNamed "hm") (expr.Rec .BAnon (.BNamed "v") (expr.Rec .BAnon (.BNamed "α")
      (Match (App (App (Val get) (Var "hm")) (Var "v"))
        .BAnon (Let (.BNamed "b") (App (Val Hr.rand_tape) (Var "α"))
          (Seq (App (App (App (Val set) (Var "hm")) (Var "v")) (Var "b")) (Var "b")))
        (.BNamed "b") (Var "b")))) :=
  rfl

/-- Sanity check: the transcription of `compute_con_hash_specialized` is the intended AST. -/
example (lhm : val) : compute_con_hash_specialized val_size lhm =
    val.RecV .BAnon (.BNamed "v") (expr.Rec .BAnon (.BNamed "α")
      (Let (.BNamed "hm") (Val lhm)
        (Let (.BNamed "l") (expr.Fst (Var "hm"))
          (Let (.BNamed "hm") (expr.Snd (Var "hm"))
            (Seq (App (Val lo.acquire) (Var "l"))
              (Let (.BNamed "output")
                (App (App (App (Val (compute_hash val_size)) (Var "hm")) (Var "v")) (Var "α"))
                (Seq (App (Val lo.release) (Var "l")) (Var "output")))))))) :=
  rfl

/-! ## Predicates -/

/-- Rocq: `hash_tape`. -/
def hash_tape (α : val) (t : List ℕ) (γ : Hr.rand_tape_name) : IProp GF :=
  Hr.rand_tapes α t γ

/-- Rocq: `abstract_con_hash`. -/
def abstract_con_hash (f l hm : val) : IProp GF :=
  iprop(⌜f = compute_con_hash_specialized val_size (PairV l hm)⌝)

/-- Rocq: `abstract_con_hash_inv`. -/
def abstract_con_hash_inv (N : Namespace) (f l hm : val) (γ_tape : Hr.rand_tape_name) :
    IProp GF :=
  iprop(abstract_con_hash val_size f l hm ∗ Hr.is_rand N γ_tape)

/-- Rocq: `concrete_con_hash`. -/
def concrete_con_hash (hm : val) (m : hmap) (R : hmap → IProp GF)
    [_HR : ∀ m, Timeless (R m)] : IProp GF :=
  iprop(∃ hm' : Loc, ⌜hm = LitV (LitLoc hm')⌝ ∗
    map_list hm' (m.map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ)))) ∗
    R m)

/-- Rocq: `concrete_con_hash_inv`. -/
def concrete_con_hash_inv (hm l : val) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)]
    (γ_lock : lo.lock_name) : IProp GF :=
  lo.is_lock L γ_lock l iprop(∃ m, concrete_con_hash hm m R)

/-- Rocq: `con_hash_inv`. -/
def con_hash_inv (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_tape : Hr.rand_tape_name) (γ_lock : lo.lock_name) :
    IProp GF :=
  iprop(abstract_con_hash_inv val_size N f l hm γ_tape ∗ concrete_con_hash_inv L hm l R γ_lock)

/-- Rocq: (the automatically solved obligation) `hash_tape_timeless`. -/
instance hash_tape_timeless (α : val) (ns : List ℕ) (γ : Hr.rand_tape_name) :
    Timeless (hash_tape val_size α ns γ : IProp GF) := by
  unfold hash_tape; infer_instance

/-- Rocq: (the automatically solved obligation) `con_hash_inv_persistent`. -/
instance con_hash_inv_persistent (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_tape : Hr.rand_tape_name) (γ_lock : lo.lock_name) :
    Persistent (con_hash_inv val_size L N f l hm R γ_tape γ_lock) := by
  unfold con_hash_inv abstract_con_hash_inv abstract_con_hash concrete_con_hash_inv
  infer_instance

/-! ## Lemmas -/

/-- Rocq: `con_hash_tape_presample`. -/
theorem con_hash_tape_presample (N : Namespace) (γ : Hr.rand_tape_name) (γ_lock : lo.lock_name)
    (f l hm : val) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] (α : val) (ns : List ℕ)
    (ε : ℝ≥0∞) (ε2 : Fin (val_size + 1) → ℝ≥0∞) (E : CoPset) (Hsubset : ↑N ⊆ E)
    (Hineq : ∑' n : Fin (val_size + 1), 1 / ((val_size : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢ con_hash_inv val_size L N f l hm R γ γ_lock -∗
      hash_tape val_size α ns γ -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (val_size + 1),
        ↯ (ε2 n) ∗ hash_tape val_size α (ns ++ [(n : ℕ)]) γ) := by
  unfold con_hash_inv abstract_con_hash_inv hash_tape
  iintro ⟨⟨-, #Hrand⟩, -⟩ Htape Herr
  imod Hr.rand_tapes_presample N E α ns ε ε2 γ Hsubset Hineq $$ Hrand Htape Herr
    with ⟨%n, Herr, Htape⟩
  imodintro
  iexists n
  iframe

/-- Rocq: `con_hash_init`. -/
theorem con_hash_init (N : Namespace) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] :
    {{ R ∅ }} cpl(&(init_hash val_size) #())
    {{ (f : val), RET f; ∃ l hm γ_tape γ_lock,
        con_hash_inv val_size L N f l hm R γ_tape γ_lock }} := by
  iintro %Φ HR HΦ
  unfold init_hash
  iapply fupd_pgl_wp
  imod Hr.rand_inv_create_spec N ⊤ CoPset.subseteq_top with ⟨%γ_tape, #Hrand⟩
  imodintro
  wp_pures
  unfold con_hash_inv abstract_con_hash_inv abstract_con_hash concrete_con_hash_inv
    concrete_con_hash
  unfold init_hash_state
  wp_apply wp_init_map $$ [] with %l Hm
  · itrivial
  wp_pures
  wp_apply lo.newlock_spec L
    iprop(∃ m, ∃ hm' : Loc, ⌜LitV (LitLoc l) = LitV (LitLoc hm')⌝ ∗
      map_list hm' (m.map (fun _ (b : ℕ) => LitV (LitInt (b : ℤ)))) ∗ R m) $$ [Hm HR]
    with %loc %γ_lock #Hl
  · iexists ∅, l
    rw [hmap_map_empty]
    iframe
    ipureintro
    rfl
  wp_pures
  unfold compute_con_hash
  wp_pures
  iapply HΦ
  imodintro
  iexists loc, LitV (LitLoc l), γ_tape, γ_lock
  iframe Hl Hrand
  ipureintro
  rfl

/-- Rocq: `con_hash_alloc_tape`. -/
theorem con_hash_alloc_tape (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_tape : Hr.rand_tape_name) (γ_lock : lo.lock_name) :
    {{ con_hash_inv val_size L N f l hm R γ_tape γ_lock }} cpl(&(allocate_tape val_size) #())
    {{ (α : val), RET α; hash_tape val_size α [] γ_tape }} := by
  unfold con_hash_inv abstract_con_hash_inv abstract_con_hash concrete_con_hash_inv
  iintro %Φ ⟨⟨%Hf, #Hinv1'⟩, #Hin2⟩ HΦ
  unfold allocate_tape
  wp_pures
  wp_apply Hr.rand_allocate_tape_spec N γ_tape ⊤ CoPset.subseteq_top $$ Hinv1'
    with %α ⟨-, Hrand⟩
  iapply HΦ
  unfold hash_tape
  iexact Hrand

/-- Rocq: `con_hash_spec`. -/
theorem con_hash_spec (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_tape : Hr.rand_tape_name) (γ_lock : lo.lock_name)
    (Q1 : ℕ → IProp GF) (Q2 : ℕ → List ℕ → IProp GF) (α : val) (v : ℕ) :
    {{ con_hash_inv val_size L N f l hm R γ_tape γ_lock ∗
        (∀ m, R m -∗ state_update ⊤ ⊤
          (match m[v]? with
           | some res => iprop(R m ∗ Q1 res)
           | none => iprop(∃ n ns, hash_tape val_size α (n :: ns) γ_tape ∗
                (hash_tape val_size α ns γ_tape ={⊤}=∗ R (m.insert v n) ∗ Q2 n ns)))) }}
      cpl(&f #v &α)
    {{ (res : ℕ), RET LitV (LitInt (res : ℤ)); Q1 res ∨ ∃ ns, Q2 res ns }} := by
  unfold con_hash_inv abstract_con_hash_inv abstract_con_hash concrete_con_hash_inv
  iintro %Φ ⟨⟨⟨%Hf, #Hinv1'⟩, #Hin2⟩, Hvs⟩ HΦ
  subst Hf
  unfold compute_con_hash_specialized
  wp_pures
  wp_apply lo.acquire_spec L γ_lock l _ $$ Hin2 with ⟨Hl, %m, Hc⟩
  unfold concrete_con_hash
  icases Hc with ⟨%hm', %Hhm, Hm, HR⟩
  subst Hhm
  wp_pures
  unfold compute_hash
  wp_pures
  wp_apply wp_get hm' _ v $$ Hm with %res ⟨Hm, %Hres⟩
  subst Hres
  rw [Std.ExtTreeMap.getElem?_map]
  cases Hlk : m[v]? with
  | some b =>
    -- hashed before
    simp only [Option.map_some, opt_to_val]
    wp_pures
    iapply state_update_pgl_wp
    imod Hvs $$ HR with Hvs
    rw [Hlk]
    icases Hvs with ⟨HR, HQ⟩
    imodintro
    wp_apply lo.release_spec L γ_lock l _ $$ [Hl Hm HR] with -
    · iframe Hin2 Hl
      iexists m, hm'
      iframe
      ipureintro
      rfl
    wp_pures
    iapply HΦ
    ileft
    iexact HQ
  | none =>
    simp only [Option.map_none, opt_to_val]
    wp_pures
    iapply state_update_pgl_wp
    imod Hvs $$ HR with Hvs
    rw [Hlk]
    icases Hvs with ⟨%n, %ns, Htape, Hvs⟩
    imodintro
    unfold hash_tape
    wp_apply Hr.rand_tape_spec_some N γ_tape ⊤ α n ns CoPset.subseteq_top $$ [Htape]
      with Htape
    · iframe Hinv1' Htape
    iapply fupd_pgl_wp
    imod Hvs $$ Htape with ⟨HR, HQ⟩
    imodintro
    wp_pures
    wp_apply wp_set hm' _ v _ $$ Hm with Hm
    wp_pures
    wp_apply lo.release_spec L γ_lock l _ $$ [HR Hm Hl] with -
    · iframe Hin2 Hl
      iexists m.insert v n, hm'
      rw [hmap_map_insert]
      iframe
      ipureintro
      rfl
    wp_pures
    iapply HΦ
    iright
    iexists ns
    iexact HQ

/-- Rocq: the first `Next Obligation` of `con_hash_impl0` (`hash_tape_valid`). -/
theorem con_hash_impl0_hash_tape_valid (α : val) (ns : List ℕ) (γ : Hr.rand_tape_name) :
    ⊢ hash_tape val_size α ns γ -∗ ⌜∀ x ∈ ns, x ≤ val_size⌝ := by
  unfold hash_tape
  iintro H
  iapply Hr.rand_tapes_valid α ns γ $$ H

/-- Rocq: the second `Next Obligation` of `con_hash_impl0` (`hash_tape_exclusive`). -/
theorem con_hash_impl0_hash_tape_exclusive (α : val) (ns ns' : List ℕ)
    (γ : Hr.rand_tape_name) :
    ⊢ hash_tape val_size α ns γ -∗ hash_tape val_size α ns' γ -∗ False := by
  unfold hash_tape
  iintro H1 H2
  iapply Hr.rand_tapes_exclusive α ns ns' γ $$ H1 H2

/-- Rocq: `con_hash_impl0` (a `Program Definition`). -/
@[instance_reducible]
def con_hash_impl0 : con_hash0 GF val_size where
  init_hash0 := init_hash val_size
  allocate_tape0 := allocate_tape val_size
  compute_hash0 := compute_hash val_size
  hash_tape_gname := Hr.rand_tape_name
  hash_lock_gname := lo.lock_name
  con_hash_inv0 N f l hm R _ γ γ_lock := con_hash_inv val_size L N f l hm R γ γ_lock
  hash_tape0 := hash_tape val_size
  hash_tape_timeless := hash_tape_timeless val_size
  con_hash_inv_persistent N f l hm R _ γ γ_lock :=
    con_hash_inv_persistent val_size L N f l hm R γ γ_lock
  hash_tape_valid := con_hash_impl0_hash_tape_valid val_size
  hash_tape_exclusive := con_hash_impl0_hash_tape_exclusive val_size
  hash_tape_presample N γ γ_lock f l hm R _ α ns ε ε2 E HN Hsum :=
    con_hash_tape_presample val_size L N γ γ_lock f l hm R α ns ε ε2 E HN Hsum
  con_hash_init0 N R _ := con_hash_init val_size L N R
  con_hash_alloc_tape0 N f l hm R _ γ_tape γ_lock :=
    con_hash_alloc_tape val_size L N f l hm R γ_tape γ_lock
  con_hash_spec0 N f l hm R _ γ_tape γ_lock Q1 Q2 α v :=
    con_hash_spec val_size L N f l hm R γ_tape γ_lock Q1 Q2 α v

end con_hash_impl

end Coneris.Examples.HashDir.ConHashImpl0
