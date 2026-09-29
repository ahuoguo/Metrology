module

public import Metrology.Foxtrot.BinaryRel.BinaryModel
public import Metrology.ConProbLang.Typing.ContextualRefinement

/-!
# The binary logical relation of Foxtrot: interpretation of types

Ported from clutch/theories/foxtrot/binary_rel/binary_interp.v

Interpretation of the syntactic types of `con_prob_lang` (System F_mu_ref_fork with tapes) as
binary semantic types `lrel GF`, the interpretation of typing environments, and the semantic
typing judgement `〈 Δ ; Γ 〉 ⊨ e ≤log≤ e' : τ`. Lives in the namespace `Foxtrot.BinaryRel`
(see `BinaryModel.lean`).

## Rocq → Lean map
* `ctx_lookup`, `interp`, `unboxed_type_sound`, `eq_type_sound`, `unboxed_type_eq`,
  `interp_ren_up`, `interp_ren`, `interp_weaken`, `interp_subst_up`, `interp_subst`,
  `env_ltyped2`, `env_ltyped2_ne`, `env_ltyped2_lookup`, `env_ltyped2_insert`,
  `env_ltyped2_empty`, `env_ltyped2_empty_inv`, `env_ltyped2_persistent`, `bin_log_related`:
  same names.
* `listO (lrelC Σ) -n> lrelC Σ` is `List (lrel GF) -n> lrel GF` (iris-lean's pointwise list OFE).
  `interp τ Δ` is `(interp τ).f Δ` (coercion of `OFE.Hom`).
* `from_option id lrel_true (Δ !! x)` is `(Δ[x]?).elim lrel_true id`.
* `(λ τ, interp τ Δ) <$> Γ` (on `stringmap type`) is `Γ.map fun _ τ => interp τ Δ`;
  `fst <$> vs` / `snd <$> vs` are `vs.map fun _ p => p.1` / `vs.map fun _ p => p.2`
  (`Std.ExtTreeMap.map` on `varmap`).
* `[∗ map] i ↦ A;vv ∈ Γ;vs, lrel_car A vv.1 vv.2` is iris-lean's `bigSepM2` over `varmap`.
* Autosubst `upn n σ` is the local definition `upn` (iterated `type.up`), with the Autosubst
  lemma `iter_up` proved locally (stated with `type.rename (· + m)`).
* Notation `⟦ Γ ⟧*` is the scoped notation for `env_ltyped2 Γ`, and
  `〈 Δ ';' Γ 〉 ⊨ e '≤log≤' e' : τ` is the scoped notation `〈 Δ ; Γ 〉 ⊨ e ≤log≤ e' : τ`.

## Deviations
* The OFEs of `lrel GF` and of lists have Leibniz equality, so Rocq's `≡` statements
  (`interp_ren_up`, `interp_ren`, `interp_weaken`, `interp_subst_up`, `interp_subst`) are
  equalities, proved by plain congruence arguments (no `properness`).
* `unboxed_type_eq`, reference case: instead of opening the two invariants by hand, the proof
  uses `interp_ref_funct`/`interp_ref_inj` from `BinaryModel` (which do exactly that).
* `env_ltyped2_ne` (a `Proper (dist n ==> (=) ==> dist n)` instance in Rocq) is a theorem whose
  hypothesis on the maps is the pointwise `Option.Rel (· ≡{n}≡ ·)` on lookups.
* `env_ltyped2_persistent` is an instance obtained from iris-lean's `bigSepM2` instances.

## Omitted
* `env_ltyped2_proper` (setoid plumbing: `≡` is `=`).
* The commented-out Rocq code (the tape case of `unboxed_type_eq`, the commented notation
  for `bin_log_related` with a mask).

## Added (not in Rocq)
* `lrel_ref_ne`, `lrel_exists_ne`, `lrel_forall_ne` (non-expansiveness of the remaining lrel
  constructors, used in the definition of `interp`; Rocq gets them from `solve_proper`).
* `lrel_rec_ext` (congruence of `lrel_rec` for pointwise-equal functors).
* `interp_TUnit`, ..., `interp_TTape` (definitional unfolding equations of `interp`).
* `upn`, `upn_zero`, `upn_succ`, `iter_up` (Autosubst; duplicates of the `Foxtrot.UnaryRel`
  versions, so that the two relations stay independent).
* `varmap_insert_eq` (iris-lean's `PartialMap.insert` on `ExtTreeMap` is `ExtTreeMap.insert`).
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

/-! ## Interpretation of types (Rocq: section `semtypes`) -/

section semtypes

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Added: `lrel_ref` is non-expansive. -/
instance lrel_ref_ne : OFE.NonExpansive (lrel_ref (GF := GF)) where
  ne {n A A'} hA w1 w2 := by
    dsimp only [lrel_ref]
    exact exists_ne fun l1 => exists_ne fun l2 => and_ne.ne .rfl <| and_ne.ne .rfl <|
      (Iris.inv_ne _).ne (exists_ne fun v1 => exists_ne fun v2 =>
        sep_ne.ne .rfl (sep_ne.ne .rfl (hA v1 v2)))

omit [foxtrotRGS GF] in
/-- Added: `lrel_exists` is non-expansive (pointwise). -/
theorem lrel_exists_ne {n : ℕ} {C C' : lrel GF → lrel GF} (h : ∀ A, C A ≡{n}≡ C' A) :
    lrel_exists C ≡{n}≡ lrel_exists C' := fun w1 w2 => by
  dsimp only [lrel_exists]
  exact exists_ne fun A => h A w1 w2

/-- Added: `lrel_forall` is non-expansive (pointwise). -/
theorem lrel_forall_ne {n : ℕ} {C C' : lrel GF → lrel GF} (h : ∀ A, C A ≡{n}≡ C' A) :
    lrel_forall C ≡{n}≡ lrel_forall C' := fun w1 w2 => by
  dsimp only [lrel_forall]
  exact forall_ne fun A => lrel_arr_ne.ne .rfl (h A) w1 w2

omit [foxtrotRGS GF] in
/-- Added: congruence of `lrel_rec` for pointwise-equal functors. -/
theorem lrel_rec_ext {C C' : lrel GF -n> lrel GF} (h : ∀ A, C A = C' A) :
    lrel_rec C = lrel_rec C' := by
  have : C = C' := OFE.Hom.ext (funext h)
  rw [this]

/-- Rocq: `ctx_lookup`. -/
def ctx_lookup (x : ℕ) : List (lrel GF) -n> lrel GF where
  f Δ := (Δ[x]?).elim lrel_true id
  ne := ⟨fun n Δ Δ' hΔ => by
    have h : Option.Forall₂ (· ≡{n}≡ ·) Δ[x]? Δ'[x]? := hΔ.getElem? x
    revert h
    cases Δ[x]? <;> cases Δ'[x]? <;> simp [Option.Forall₂, Option.elim]⟩

/-- Rocq: `interp`. -/
def interp : type → List (lrel GF) -n> lrel GF
  | TUnit => { f := fun _ => lrel_unit, ne := ⟨fun _ _ _ _ => .rfl⟩ }
  | TNat => { f := fun _ => lrel_nat, ne := ⟨fun _ _ _ _ => .rfl⟩ }
  | TInt => { f := fun _ => lrel_int, ne := ⟨fun _ _ _ _ => .rfl⟩ }
  | TBool => { f := fun _ => lrel_bool, ne := ⟨fun _ _ _ _ => .rfl⟩ }
  | TProd τ1 τ2 =>
    { f := fun Δ => lrel_prod (interp τ1 Δ) (interp τ2 Δ)
      ne := ⟨fun _ _ _ h => lrel_prod_ne.ne ((interp τ1).ne.ne h) ((interp τ2).ne.ne h)⟩ }
  | TSum τ1 τ2 =>
    { f := fun Δ => lrel_sum (interp τ1 Δ) (interp τ2 Δ)
      ne := ⟨fun _ _ _ h => lrel_sum_ne.ne ((interp τ1).ne.ne h) ((interp τ2).ne.ne h)⟩ }
  | TArrow τ1 τ2 =>
    { f := fun Δ => lrel_arr (interp τ1 Δ) (interp τ2 Δ)
      ne := ⟨fun _ _ _ h => lrel_arr_ne.ne ((interp τ1).ne.ne h) ((interp τ2).ne.ne h)⟩ }
  | TRec τ' =>
    { f := fun Δ => lrel_rec
        { f := fun τ => interp τ' (τ :: Δ)
          ne := ⟨fun _ _ _ h => (interp τ').ne.ne (.cons h (List.Forall₂.rfl .refl))⟩ }
      ne := ⟨fun _ _ _ h => lrel_rec_ne fun _ => (interp τ').ne.ne (.cons .rfl h)⟩ }
  | TVar x => ctx_lookup x
  | TForall τ' =>
    { f := fun Δ => lrel_forall (fun τ => interp τ' (τ :: Δ))
      ne := ⟨fun _ _ _ h => lrel_forall_ne fun _ => (interp τ').ne.ne (.cons .rfl h)⟩ }
  | TExists τ' =>
    { f := fun Δ => lrel_exists (fun τ => interp τ' (τ :: Δ))
      ne := ⟨fun _ _ _ h => lrel_exists_ne fun _ => (interp τ').ne.ne (.cons .rfl h)⟩ }
  | TRef τ =>
    { f := fun Δ => lrel_ref (interp τ Δ)
      ne := ⟨fun _ _ _ h => lrel_ref_ne.ne ((interp τ).ne.ne h)⟩ }
  | TTape => { f := fun _ => lrel_tape, ne := ⟨fun _ _ _ _ => .rfl⟩ }

/-! Added: definitional unfolding equations of `interp`. -/

section interp_eqns
variable (Δ : List (lrel GF))

theorem interp_TUnit : interp TUnit Δ = lrel_unit := rfl
theorem interp_TNat : interp TNat Δ = lrel_nat := rfl
theorem interp_TInt : interp TInt Δ = lrel_int := rfl
theorem interp_TBool : interp TBool Δ = lrel_bool := rfl
theorem interp_TProd (τ1 τ2 : type) :
    interp (TProd τ1 τ2) Δ = lrel_prod (interp τ1 Δ) (interp τ2 Δ) := rfl
theorem interp_TSum (τ1 τ2 : type) :
    interp (TSum τ1 τ2) Δ = lrel_sum (interp τ1 Δ) (interp τ2 Δ) := rfl
theorem interp_TArrow (τ1 τ2 : type) :
    interp (TArrow τ1 τ2) Δ = lrel_arr (interp τ1 Δ) (interp τ2 Δ) := rfl
theorem interp_TRec (τ' : type) :
    interp (TRec τ') Δ = lrel_rec
      { f := fun τ => interp τ' (τ :: Δ)
        ne := ⟨fun _ _ _ h => (interp τ').ne.ne (.cons h (List.Forall₂.rfl .refl))⟩ } := rfl
theorem interp_TVar (x : ℕ) : interp (TVar x) Δ = (Δ[x]?).elim lrel_true id := rfl
theorem interp_TForall (τ' : type) :
    interp (TForall τ') Δ = lrel_forall (fun τ => interp τ' (τ :: Δ)) := rfl
theorem interp_TExists (τ' : type) :
    interp (TExists τ') Δ = lrel_exists (fun τ => interp τ' (τ :: Δ)) := rfl
theorem interp_TRef (τ : type) : interp (TRef τ) Δ = lrel_ref (interp τ Δ) := rfl
theorem interp_TTape : interp TTape Δ = lrel_tape := rfl

end interp_eqns

/-- Rocq: `unboxed_type_sound`. -/
theorem unboxed_type_sound (τ : type) (Δ : List (lrel GF)) (v v' : val) :
    UnboxedType τ → interp τ Δ v v' ⊢ ⌜val_is_unboxed v ∧ val_is_unboxed v'⌝ := by
  intro h
  cases h with
  | UnboxedTUnit =>
    show iprop(⌜v = LitV LitUnit ∧ v' = LitV LitUnit⌝) ⊢ _
    iintro %hv !%
    obtain ⟨rfl, rfl⟩ := hv; exact ⟨trivial, trivial⟩
  | UnboxedTNat =>
    show iprop(∃ n : ℕ, ⌜v = LitV (LitInt (n : ℤ)) ∧ v' = LitV (LitInt (n : ℤ))⌝) ⊢ _
    iintro ⟨%n, %hv⟩ !%
    obtain ⟨rfl, rfl⟩ := hv; exact ⟨trivial, trivial⟩
  | UnboxedTInt =>
    show iprop(∃ n : ℤ, ⌜v = LitV (LitInt n) ∧ v' = LitV (LitInt n)⌝) ⊢ _
    iintro ⟨%n, %hv⟩ !%
    obtain ⟨rfl, rfl⟩ := hv; exact ⟨trivial, trivial⟩
  | UnboxedTBool =>
    show iprop(∃ b : Bool, ⌜v = LitV (LitBool b) ∧ v' = LitV (LitBool b)⌝) ⊢ _
    iintro ⟨%b, %hv⟩ !%
    obtain ⟨rfl, rfl⟩ := hv; exact ⟨trivial, trivial⟩
  | UnboxedTRef τ =>
    rw [interp_TRef]
    unfold lrel_ref
    iintro ⟨%l1, %l2, %hv, %hv', -⟩ !%
    subst hv hv'; exact ⟨trivial, trivial⟩

/-- Rocq: `eq_type_sound`. -/
theorem eq_type_sound (τ : type) (Δ : List (lrel GF)) (v v' : val) :
    EqType τ → interp τ Δ v v' ⊢ ⌜v = v'⌝ := by
  intro hτ
  induction hτ generalizing v v' with
  | EqTUnit =>
    show iprop(⌜v = LitV LitUnit ∧ v' = LitV LitUnit⌝) ⊢ _
    iintro %hv !%
    rw [hv.1, hv.2]
  | EqTNat =>
    show iprop(∃ n : ℕ, ⌜v = LitV (LitInt (n : ℤ)) ∧ v' = LitV (LitInt (n : ℤ))⌝) ⊢ _
    iintro ⟨%n, %hv⟩ !%
    rw [hv.1, hv.2]
  | EqTInt =>
    show iprop(∃ n : ℤ, ⌜v = LitV (LitInt n) ∧ v' = LitV (LitInt n)⌝) ⊢ _
    iintro ⟨%n, %hv⟩ !%
    rw [hv.1, hv.2]
  | EqTBool =>
    show iprop(∃ b : Bool, ⌜v = LitV (LitBool b) ∧ v' = LitV (LitBool b)⌝) ⊢ _
    iintro ⟨%b, %hv⟩ !%
    rw [hv.1, hv.2]
  | EqTProd τ1 τ2 _ _ ih1 ih2 =>
    rw [interp_TProd]
    unfold lrel_prod
    iintro ⟨%a1, %a2, %b1, %b2, %h1, %h2, HA, HB⟩
    ihave %heq1 := ih1 a1 a2 $$ HA
    ihave %heq2 := ih2 b1 b2 $$ HB
    ipureintro
    rw [h1, h2, heq1, heq2]
  | EqSum τ1 τ2 _ _ ih1 ih2 =>
    rw [interp_TSum]
    unfold lrel_sum
    iintro ⟨%w1, %w2, Hd⟩
    icases Hd with (⟨%h1, %h2, HA⟩ | ⟨%h1, %h2, HB⟩)
    · ihave %heq := ih1 w1 w2 $$ HA
      ipureintro
      rw [h1, h2, heq]
    · ihave %heq := ih2 w1 w2 $$ HB
      ipureintro
      rw [h1, h2, heq]

/-- Rocq: `unboxed_type_eq`. -/
theorem unboxed_type_eq (τ : type) (Δ : List (lrel GF)) (v1 v2 w1 w2 : val) :
    UnboxedType τ →
    interp τ Δ v1 v2 ⊢ interp τ Δ w1 w2 -∗ |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝ := by
  intro hunboxed
  rcases unboxed_type_ref_or_eqtype τ hunboxed with hτ | ⟨τ', rfl⟩
  · iintro H1 H2
    ihave %heq1 := eq_type_sound τ Δ v1 v2 hτ $$ H1
    ihave %heq2 := eq_type_sound τ Δ w1 w2 hτ $$ H2
    imodintro
    ipureintro
    subst heq1 heq2
    exact .rfl
  · rw [interp_TRef]
    iintro #H1 #H2
    ihave %hs1 : iprop(⌜∃ l1 l2 : Loc, v1 = LitV (LitLoc l1) ∧ v2 = LitV (LitLoc l2)⌝) $$ [H1]
    · unfold lrel_ref
      icases H1 with ⟨%l1, %l2, %h1, %h2, -⟩
      ipureintro; exact ⟨l1, l2, h1, h2⟩
    ihave %hs2 : iprop(⌜∃ r1 r2 : Loc, w1 = LitV (LitLoc r1) ∧ w2 = LitV (LitLoc r2)⌝) $$ [H2]
    · unfold lrel_ref
      icases H2 with ⟨%r1, %r2, %h1, %h2, -⟩
      ipureintro; exact ⟨r1, r2, h1, h2⟩
    obtain ⟨l1, l2, rfl, rfl⟩ := hs1
    obtain ⟨r1, r2, rfl, rfl⟩ := hs2
    simp only [val.LitV.injEq, base_lit.LitLoc.injEq]
    by_cases hl : l1 = r1
    · subst hl
      imod interp_ref_funct ⊤ (interp τ' Δ) l1 l2 r2 CoPset.subseteq_top $$ [H1 H2] with %h
      · isplitl [H1]
        · iexact H1
        · iexact H2
      imodintro
      ipureintro
      simp [h]
    · by_cases hr : l2 = r2
      · subst hr
        imod interp_ref_inj ⊤ (interp τ' Δ) l2 l1 r1 CoPset.subseteq_top $$ [H1 H2] with %h
        · isplitl [H1]
          · iexact H1
          · iexact H2
        exact (hl h).elim
      · imodintro
        ipureintro
        exact iff_of_false hl hr

end semtypes

/-! ## Autosubst's `upn` (added) -/

/-- Autosubst `upn n σ`: `σ` lifted under `n` binders. -/
def upn : ℕ → (ℕ → type) → ℕ → type
  | 0, σ => σ
  | n + 1, σ => type.up (upn n σ)

@[simp] theorem upn_zero (σ : ℕ → type) : upn 0 σ = σ := rfl
@[simp] theorem upn_succ (n : ℕ) (σ : ℕ → type) : upn (n + 1) σ = type.up (upn n σ) := rfl

/-- Autosubst `iter_up`. -/
theorem iter_up (m x : ℕ) (σ : ℕ → type) :
    upn m σ x = if x < m then TVar x else type.rename (· + m) (σ (x - m)) := by
  induction m generalizing x with
  | zero =>
    simp only [upn_zero, Nat.not_lt_zero, ite_false, Nat.sub_zero, Nat.add_zero]
    have : (fun y : ℕ => y) = id := rfl
    rw [this, type.rename_subst]
    change σ x = type.subst type.ids (σ x)
    rw [type.subst_id]
  | succ m ih =>
    cases x with
    | zero => simp [upn_succ]
    | succ x =>
      simp only [upn_succ, type.up_succ, ih]
      by_cases hx : x < m
      · simp [hx, type.rename]
      · have hx' : ¬ x + 1 < m + 1 := by omega
        simp only [hx, hx', ite_false, type.rename_rename]
        have h1 : x + 1 - (m + 1) = x - m := by omega
        rw [h1]
        congr 1

/-! ## Properties of the type interpretation w.r.t. substitutions (Rocq: `interp_ren`) -/

section interp_ren

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `interp_ren_up`. -/
theorem interp_ren_up (Δ1 Δ2 : List (lrel GF)) (τ : type) (τi : lrel GF) :
    interp τ (Δ1 ++ Δ2) =
      interp (type.subst (upn Δ1.length (type.ren (· + 1))) τ) (Δ1 ++ τi :: Δ2) := by
  induction τ generalizing Δ1 with
  | TUnit | TNat | TInt | TBool | TTape => rfl
  | TProd τ1 τ2 ih1 ih2 =>
    simp only [type.subst, interp_TProd]; rw [← ih1, ← ih2]
  | TSum τ1 τ2 ih1 ih2 =>
    simp only [type.subst, interp_TSum]; rw [← ih1, ← ih2]
  | TArrow τ1 τ2 ih1 ih2 =>
    simp only [type.subst, interp_TArrow]; rw [← ih1, ← ih2]
  | TRef τ ih =>
    simp only [type.subst, interp_TRef]; rw [← ih]
  | TRec τ ih =>
    simp only [type.subst, interp_TRec]
    exact lrel_rec_ext fun A => ih (A :: Δ1)
  | TForall τ ih =>
    simp only [type.subst, interp_TForall]
    exact congrArg lrel_forall (funext fun A => ih (A :: Δ1))
  | TExists τ ih =>
    simp only [type.subst, interp_TExists]
    exact congrArg lrel_exists (funext fun A => ih (A :: Δ1))
  | TVar x =>
    simp only [type.subst, iter_up]
    split
    · rename_i hx
      simp only [interp_TVar, List.getElem?_append_left hx]
    · rename_i hx
      simp only [type.rename, interp_TVar]
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      have : x - Δ1.length + 1 + Δ1.length - Δ1.length = (x - Δ1.length) + 1 := by omega
      rw [this, List.getElem?_cons_succ]

/-- Rocq: `interp_ren`. -/
theorem interp_ren (A : lrel GF) (Δ : List (lrel GF)) (Γ : varmap type) :
    (⤉Γ).map (fun _ τ => interp τ (A :: Δ)) = Γ.map (fun _ τ => interp τ Δ) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro x
  simp only [Std.ExtTreeMap.getElem?_map, lookup_type_shift_ctx]
  cases Γ[x]? with
  | none => rfl
  | some τ =>
    simp only [Option.map_some]
    exact congrArg some (interp_ren_up [] Δ τ A).symm

/-- Rocq: `interp_weaken`. -/
theorem interp_weaken (Δ1 Pi Δ2 : List (lrel GF)) (τ : type) :
    interp (type.subst (upn Δ1.length (type.ren (· + Pi.length))) τ) (Δ1 ++ Pi ++ Δ2) =
      interp τ (Δ1 ++ Δ2) := by
  induction τ generalizing Δ1 with
  | TUnit | TNat | TInt | TBool | TTape => rfl
  | TProd τ1 τ2 ih1 ih2 =>
    simp only [type.subst, interp_TProd]; rw [ih1, ih2]
  | TSum τ1 τ2 ih1 ih2 =>
    simp only [type.subst, interp_TSum]; rw [ih1, ih2]
  | TArrow τ1 τ2 ih1 ih2 =>
    simp only [type.subst, interp_TArrow]; rw [ih1, ih2]
  | TRef τ ih =>
    simp only [type.subst, interp_TRef]; rw [ih]
  | TRec τ ih =>
    simp only [type.subst, interp_TRec]
    exact lrel_rec_ext fun A => ih (A :: Δ1)
  | TForall τ ih =>
    simp only [type.subst, interp_TForall]
    exact congrArg lrel_forall (funext fun A => ih (A :: Δ1))
  | TExists τ ih =>
    simp only [type.subst, interp_TExists]
    exact congrArg lrel_exists (funext fun A => ih (A :: Δ1))
  | TVar x =>
    simp only [type.subst, iter_up, List.append_assoc]
    split
    · rename_i hx
      simp only [interp_TVar, List.getElem?_append_left hx]
    · rename_i hx
      simp only [type.rename, interp_TVar]
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        List.getElem?_append_right (by omega)]
      congr 2
      omega

/-- Rocq: `interp_subst_up`. -/
theorem interp_subst_up (Δ1 Δ2 : List (lrel GF)) (τ τ' : type) :
    interp τ (Δ1 ++ interp τ' Δ2 :: Δ2) =
      interp (type.subst (upn Δ1.length (type.scons τ' type.ids)) τ) (Δ1 ++ Δ2) := by
  induction τ generalizing Δ1 with
  | TUnit | TNat | TInt | TBool | TTape => rfl
  | TProd τ1 τ2 ih1 ih2 =>
    simp only [type.subst, interp_TProd]; rw [ih1, ih2]
  | TSum τ1 τ2 ih1 ih2 =>
    simp only [type.subst, interp_TSum]; rw [ih1, ih2]
  | TArrow τ1 τ2 ih1 ih2 =>
    simp only [type.subst, interp_TArrow]; rw [ih1, ih2]
  | TRef τ ih =>
    simp only [type.subst, interp_TRef]; rw [ih]
  | TRec τ ih =>
    simp only [type.subst, interp_TRec]
    exact lrel_rec_ext fun A => ih (A :: Δ1)
  | TForall τ ih =>
    simp only [type.subst, interp_TForall]
    exact congrArg lrel_forall (funext fun A => ih (A :: Δ1))
  | TExists τ ih =>
    simp only [type.subst, interp_TExists]
    exact congrArg lrel_exists (funext fun A => ih (A :: Δ1))
  | TVar x =>
    simp only [type.subst, iter_up]
    split
    · rename_i hx
      simp only [interp_TVar, List.getElem?_append_left hx]
    · rename_i hx
      rw [interp_TVar, List.getElem?_append_right (by omega)]
      rcases hEQ : x - Δ1.length with _ | n
      · simp only [List.getElem?_cons_zero, Option.elim, type.scons_zero, id]
        have HW := interp_weaken [] Δ1 Δ2 τ'
        simp only [List.length_nil, upn_zero, List.nil_append] at HW
        rw [← HW, type.rename_subst]
      · simp only [List.getElem?_cons_succ, type.scons_succ, type.ids, type.rename,
          interp_TVar]
        rw [List.getElem?_append_right (by omega)]
        congr 3
        omega

/-- Rocq: `interp_subst`. -/
theorem interp_subst (Δ2 : List (lrel GF)) (τ τ' : type) :
    interp τ (interp τ' Δ2 :: Δ2) = interp (τ.[τ'/]) Δ2 :=
  interp_subst_up [] Δ2 τ τ'

end interp_ren

/-! ## Interpretation of the environments (Rocq: section `env_typed`) -/

section env_typed

variable {GF : BundledGFunctors}

/-- Rocq: `env_ltyped2`. Substitution `vs` is well-typed w.r.t. `Γ`. -/
def env_ltyped2 (Γ : varmap (lrel GF)) (vs : varmap (val × val)) : IProp GF :=
  [∗map] _i ↦ A;vv ∈ Γ;vs, A vv.1 vv.2

/-- Rocq: notation `⟦ Γ ⟧*`. -/
scoped notation "⟦ " Γ " ⟧*" => env_ltyped2 Γ

/-- Added: iris-lean's `PartialMap.insert` on `varmap` is `ExtTreeMap.insert`. -/
theorem varmap_insert_eq {V : Type} (m : varmap V) (x : String) (v : V) :
    Iris.Std.insert m x v = m.insert x v := by
  apply Std.ExtTreeMap.ext_getElem?
  intro y
  show (m.alter x (fun _ => some v))[y]? = _
  simp only [Std.ExtTreeMap.getElem?_alter, Std.ExtTreeMap.getElem?_insert]

/-- Rocq: `env_ltyped2_ne`. -/
theorem env_ltyped2_ne (n : ℕ) {Γ Γ' : varmap (lrel GF)}
    (hΓ : ∀ k : String, Option.Rel (fun x y => x ≡{n}≡ y) Γ[k]? Γ'[k]?) (vs : varmap (val × val)) :
    env_ltyped2 Γ vs ≡{n}≡ env_ltyped2 Γ' vs := by
  let _ : OFE (val × val) := OFE.ofDiscrete (val × val)
  refine BigSepM2.bigSepM2_dist_2 (lrel GF) (val × val) _ _ Γ vs Γ' vs n hΓ ?_ ?_
  · intro k
    show Option.Rel _ vs[k]? vs[k]?
    cases vs[k]? <;> constructor; rfl
  · intro k x1 x1' x2 x2' _ _ hx1 _ _ hx2
    have : x2 = x2' := hx2
    subst this
    exact hx1 x2.1 x2.2

/-- Rocq: `env_ltyped2_lookup`. -/
theorem env_ltyped2_lookup (Γ : varmap (lrel GF)) (vs : varmap (val × val)) (x : String)
    (A : lrel GF) (h : Γ[x]? = some A) :
    ⟦ Γ ⟧* vs ⊢ ∃ v1 v2, ⌜vs[x]? = some (v1, v2)⌝ ∧ A v1 v2 := by
  refine (BigSepM2.bigSepM2_lookup_left
    (Φ := fun _ (A : lrel GF) (vv : val × val) => A vv.1 vv.2) (m2 := vs) h).trans ?_
  iintro ⟨%vv, %hvv, HA⟩
  iexists vv.1, vv.2
  isplitr
  · ipureintro; exact hvv
  · iexact HA

/-- Rocq: `env_ltyped2_insert`. -/
theorem env_ltyped2_insert (Γ : varmap (lrel GF)) (vs : varmap (val × val)) (x : binder)
    (A : lrel GF) (v1 v2 : val) :
    A v1 v2 ⊢ ⟦ Γ ⟧* vs -∗ ⟦ binder_insert x A Γ ⟧* (binder_insert x (v1, v2) vs) := by
  cases x with
  | BAnon =>
    show _ ⊢ ⟦ Γ ⟧* vs -∗ ⟦ Γ ⟧* vs
    iintro _ H
    iexact H
  | BNamed x =>
    have h := BigSepM2.bigSepM2_insert_elim
      (Φ := fun _ (A : lrel GF) (vv : val × val) => A vv.1 vv.2)
      (m1 := Γ) (m2 := vs) (i := x) (x1 := A) (x2 := (v1, v2))
    rw [varmap_insert_eq, varmap_insert_eq] at h
    exact wand_entails h

/-- Rocq: `env_ltyped2_empty`. -/
theorem env_ltyped2_empty : ⊢ ⟦ (∅ : varmap (lrel GF)) ⟧* (∅ : varmap (val × val)) :=
  (BigSepM2.bigSepM2_empty (Φ := fun _ (A : lrel GF) (vv : val × val) => A vv.1 vv.2)).2

/-- Rocq: `env_ltyped2_empty_inv`. -/
theorem env_ltyped2_empty_inv (vs : varmap (val × val)) :
    ⟦ (∅ : varmap (lrel GF)) ⟧* vs ⊢ ⌜vs = ∅⌝ :=
  BigSepM2.bigSepM2_empty_right (Φ := fun _ (A : lrel GF) (vv : val × val) => A vv.1 vv.2) vs

/-- Rocq: `env_ltyped2_persistent`. -/
instance env_ltyped2_persistent (Γ : varmap (lrel GF)) (vs : varmap (val × val)) :
    Persistent (⟦ Γ ⟧* vs) := by
  unfold env_ltyped2
  infer_instance

end env_typed

/-! ## The semantic typing judgement (Rocq: section `bin_log_related`) -/

section bin_log_related

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `bin_log_related`. -/
def bin_log_related (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr) (τ : type) :
    IProp GF :=
  iprop(∀ vs, ⟦ Γ.map (fun _ τ => interp τ Δ) ⟧* vs -∗
    REL subst_map (vs.map fun _ p => p.1) e << subst_map (vs.map fun _ p => p.2) e' :
      interp τ Δ)

end bin_log_related

/-- Rocq: notation `〈 Δ ';' Γ 〉 ⊨ e '≤log≤' e' : τ`. -/
scoped notation:100 "〈 " Δ " ; " Γ " 〉 " " ⊨ " e " ≤log≤ " e' " : " τ =>
  bin_log_related Δ Γ e e' τ

end Foxtrot.BinaryRel
