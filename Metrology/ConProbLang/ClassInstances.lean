module

public import Metrology.ConProbLang.Tactics

/-!
# Class instances for `con_prob_lang`

Ported from clutch/theories/con_prob_lang/class_instances.v

`IntoVal`, `AsVal`, `Atomic` and `PureExec` instances for `con_prob_lang`, mirroring
iris-lean's `Iris/HeapLang/Instances.lean`. All instances are stated for the language
`con_prob_lang`, which has to be given explicitly (`(Λ := con_prob_lang)`), since it cannot be
inferred from `expr` (in Rocq it is found through canonical structures), e.g.
`PureExec (Λ := con_prob_lang) True 1 (Fst (Val (PairV v1 v2))) (Val v1)`.

## Rocq → Lean mapping
* Instance names are the Rocq names (`into_val_val`, `as_val_val`, `rec_atomic`, ...,
  `pure_recc`, ..., `pure_tick`).
* The local Ltacs `solve_atomic`, `solve_exec_safe`, `solve_exec_puredet`, `solve_pure_exec`
  are replaced by the helper lemmas `atomic_of_head_step_rel` and `pure_exec_of_head_step`
  (not in Rocq) together with local macros `solve_atomic`, `solve_pure_exec`.
* `AsRecV v f x erec` is a class with `outParam`s `f x erec`; the Rocq `Hint Extern` restricting
  `AsRecV_recv` to syntactic `RecV`s is the plain instance `AsRecV_recv`: Lean's instance search
  only unfolds reducible definitions, so (as in Rocq) values hidden behind a (non-reducible)
  definition are not reduced by `pure_beta`. `Hint Mode AsRecV ! - - -` is implied by the
  `outParam`s.
* Instance priorities: Rocq's cost `| 1` for `pure_eqop` and `| 10` for `pure_binop` become
  `priority := default + 10` for `pure_eqop` (tried before `pure_binop_eval`).
* `pure_unop`, `pure_binop` have a variable (`v'`) only occurring in the output (`outParam`)
  arguments of `PureExec`; Lean's instance search never determines such a variable (Rocq's
  `wp_pure` unifies it when solving `φ` by `reflexivity`). They are therefore stated as
  theorems with the Rocq shape, and the instances are the computing variants
  `pure_unop_eval : PureExec ((un_op_eval op v).isSome = true) 1 (UnOp op (Val v))
  (Val ((un_op_eval op v).getD v))` and `pure_binop_eval` (not in Rocq); `pure_unop_eval_iff` /
  `pure_binop_eval_iff` relate the computed form back to the Rocq one. Downstream `wp_pure`
  tactics discharge `φ` by `decide`/`simp` and normalize the result with `simp`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang
namespace con_prob_lang

/-- Rocq: `into_val_val`. -/
instance into_val_val (v : val) : IntoVal (Λ := con_prob_lang) (Val v) v := ⟨rfl⟩

/-- Rocq: `as_val_val`. -/
instance as_val_val (v : val) : AsVal (Λ := con_prob_lang) (Val v) := ⟨⟨v, rfl⟩⟩

/-! ## Instances of the `Atomic` class -/

section atomic

/-- Helper (not in Rocq; the core of Rocq's local `solve_atomic`): an expression is atomic if all
its head steps result in values and all its sub-redexes are values. -/
theorem atomic_of_head_step_rel (s : atomicity) (e : expr)
    (hatom : ∀ σ e' σ' efs, head_step_rel e σ e' σ' efs → ∃ v, to_val e' = some v)
    (hsub : ∀ Ki e', e = fill_item Ki e' → ∃ v, to_val e' = some v) :
    Atomic (Λ := con_prob_lang) s e := by
  have : Atomic (Λ := con_prob_lang) .StronglyAtomic e :=
    conEctxLanguage.ectx_language_atomic (Λ := con_prob_ectx_lang) .StronglyAtomic e
      (fun σ e' σ' efs h => hatom _ _ _ _ ((head_step_support_equiv_rel _ _ _ _ _).1 h))
      (conEctxiLanguage.ectxi_language_sub_redexes_are_values (Λ := con_prob_ectxi_lang) e hsub)
  exact strongly_atomic_atomic (Λ := con_prob_lang) e s

/-- Rocq: the local tactic `solve_atomic`. -/
local macro "solve_atomic" : tactic => `(tactic|
  (apply atomic_of_head_step_rel
   · intro σ e' σ' efs h
     simp only [to_val_eq_some_iff]
     cases h <;> simp_all [subst]
   · intro Ki e' h
     simp only [to_val_eq_some_iff]
     cases Ki <;> simp [fill_item] at h <;> aesop))

/-- Rocq: `rec_atomic`. -/
instance rec_atomic (s : atomicity) (f x : binder) (e : expr) :
    Atomic (Λ := con_prob_lang) s (Rec f x e) := by solve_atomic
/-- Rocq: `injl_atomic`. -/
instance injl_atomic (s : atomicity) (v : val) :
    Atomic (Λ := con_prob_lang) s (InjL (Val v)) := by solve_atomic
/-- Rocq: `injr_atomic`. -/
instance injr_atomic (s : atomicity) (v : val) :
    Atomic (Λ := con_prob_lang) s (InjR (Val v)) := by solve_atomic
/-- Rocq: `beta_atomic`. The instance below is a more general version of `Skip`. -/
instance beta_atomic (s : atomicity) (f x : binder) (v1 v2 : val) :
    Atomic (Λ := con_prob_lang) s (App (Val (RecV f x (Val v1))) (Val v2)) := by
  cases f <;> cases x <;> solve_atomic

/-- Rocq: `unop_atomic`. -/
instance unop_atomic (s : atomicity) (op : un_op) (v : val) :
    Atomic (Λ := con_prob_lang) s (UnOp op (Val v)) := by solve_atomic
/-- Rocq: `binop_atomic`. -/
instance binop_atomic (s : atomicity) (op : bin_op) (v1 v2 : val) :
    Atomic (Λ := con_prob_lang) s (BinOp op (Val v1) (Val v2)) := by solve_atomic
/-- Rocq: `if_true_atomic`. -/
instance if_true_atomic (s : atomicity) (v1 : val) (e2 : expr) :
    Atomic (Λ := con_prob_lang) s (If (Val <| LitV <| LitBool true) (Val v1) e2) := by
  solve_atomic
/-- Rocq: `if_false_atomic`. -/
instance if_false_atomic (s : atomicity) (e1 : expr) (v2 : val) :
    Atomic (Λ := con_prob_lang) s (If (Val <| LitV <| LitBool false) e1 (Val v2)) := by
  solve_atomic

/-- Rocq: `fst_atomic`. -/
instance fst_atomic (s : atomicity) (v : val) :
    Atomic (Λ := con_prob_lang) s (Fst (Val v)) := by solve_atomic
/-- Rocq: `snd_atomic`. -/
instance snd_atomic (s : atomicity) (v : val) :
    Atomic (Λ := con_prob_lang) s (Snd (Val v)) := by solve_atomic

/-- Rocq: `alloc_atomic`. -/
instance alloc_atomic (s : atomicity) (v : val) :
    Atomic (Λ := con_prob_lang) s (Alloc (Val v)) := by solve_atomic
/-- Rocq: `load_atomic`. -/
instance load_atomic (s : atomicity) (v : val) :
    Atomic (Λ := con_prob_lang) s (Load (Val v)) := by solve_atomic
/-- Rocq: `store_atomic`. -/
instance store_atomic (s : atomicity) (v1 v2 : val) :
    Atomic (Λ := con_prob_lang) s (Store (Val v1) (Val v2)) := by solve_atomic

/-- Rocq: `rand_atomic`. -/
instance rand_atomic (s : atomicity) (z : ℤ) (l : Loc) :
    Atomic (Λ := con_prob_lang) s (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))) := by
  solve_atomic
/-- Rocq: `rand_atomic_int`. -/
instance rand_atomic_int (s : atomicity) (z : ℤ) :
    Atomic (Λ := con_prob_lang) s (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) := by
  solve_atomic
/-- Rocq: `alloc_tape_atomic`. -/
instance alloc_tape_atomic (s : atomicity) (z : ℤ) :
    Atomic (Λ := con_prob_lang) s (AllocTape (Val (LitV (LitInt z)))) := by solve_atomic

/-- Rocq: `tick_atomic`. -/
instance tick_atomic (s : atomicity) (z : ℤ) :
    Atomic (Λ := con_prob_lang) s (Tick (Val (LitV (LitInt z)))) := by solve_atomic
/-- Rocq: `fork_atomic`. -/
instance fork_atomic (s : atomicity) (e : expr) :
    Atomic (Λ := con_prob_lang) s (Fork e) := by solve_atomic

/-- Rocq: `CmpXchg_atomic`. -/
instance CmpXchg_atomic (s : atomicity) (v0 v1 v2 : val) :
    Atomic (Λ := con_prob_lang) s (CmpXchg (Val v0) (Val v1) (Val v2)) := by solve_atomic
/-- Rocq: `xchg_atomic`. -/
instance xchg_atomic (s : atomicity) (v1 v2 : val) :
    Atomic (Λ := con_prob_lang) s (Xchg (Val v1) (Val v2)) := by solve_atomic
/-- Rocq: `faa_atomic`. -/
instance faa_atomic (s : atomicity) (v1 v2 : val) :
    Atomic (Λ := con_prob_lang) s (FAA (Val v1) (Val v2)) := by solve_atomic

end atomic

/-! ## Instances of the `PureExec` class

The behavior of the various `wp_` tactics with regard to lambda differs in the following way:

- `wp_pures` does *not* reduce lambdas/recs that are hidden behind a definition.
- `wp_rec` and `wp_lam` reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class `AsRecV v f x erec`, which takes a value `v` as
its input, and turns it into a `RecV f x erec` via the instance
`AsRecV_recv : AsRecV (RecV f x e) f x e`. In Lean, instance search only unfolds reducible
definitions, so this instance is only used if `v` is syntactically (up to reducible
unfolding) a lambda/rec, and not if `v` contains a lambda/rec that is hidden behind a
definition.

To make sure that `wp_rec` and `wp_lam` do reduce lambdas/recs that are hidden behind a
definition, these tactics have to unfold the definition first. -/

/-- Rocq: `AsRecV`. -/
class AsRecV (v : val) (f x : outParam binder) (erec : outParam expr) : Prop where
  as_recv : v = RecV f x erec

export AsRecV (as_recv)

/-- Rocq: `AsRecV_recv`. -/
instance AsRecV_recv (f x : binder) (e : expr) : AsRecV (RecV f x e) f x e := ⟨rfl⟩

section pure_exec

/-- Helper (not in Rocq; the core of Rocq's local `solve_pure_exec`): a deterministic,
state-independent, always-enabled head step is a pure step. -/
theorem pure_exec_of_head_step (φ : Prop) (e1 e2 : expr)
    (hsafe : φ → ∀ σ, ∃ e' σ' efs, head_step_rel e1 σ e' σ' efs)
    (hdet : φ → ∀ σ, head_step e1 σ (e2, σ, []) = 1) :
    PureExec (Λ := con_prob_lang) φ 1 e1 e2 := by
  refine ⟨fun hφ => nsteps.nsteps_l 0 _ _ _ ?_ (nsteps.nsteps_O _)⟩
  refine conEctxLanguage.pure_head_step_pure_step (Λ := con_prob_ectx_lang) e1 e2
    ⟨fun σ => ?_, hdet hφ⟩
  obtain ⟨e', σ', efs, h⟩ := hsafe hφ σ
  exact head_reducible_of_rel h

/-- Rocq: the local tactics `solve_exec_safe`, `solve_exec_puredet`, `solve_pure_exec`. -/
local macro "solve_pure_exec" : tactic => `(tactic|
  (apply pure_exec_of_head_step
   · intro hφ σ
     exact ⟨_, _, _, by solve_head_step_rel⟩
   · intro hφ σ
     simp_all [head_step, dret_1_1]))

/-- Rocq: `pure_recc`. -/
instance pure_recc (f x : binder) (erec : expr) :
    PureExec (Λ := con_prob_lang) True 1 (Rec f x erec) (Val <| RecV f x erec) := by
  solve_pure_exec

/-- Rocq: `pure_pairc`. -/
instance pure_pairc (v1 v2 : val) :
    PureExec (Λ := con_prob_lang) True 1 (Pair (Val v1) (Val v2)) (Val <| PairV v1 v2) := by
  solve_pure_exec
/-- Rocq: `pure_injlc`. -/
instance pure_injlc (v : val) :
    PureExec (Λ := con_prob_lang) True 1 (InjL <| Val v) (Val <| InjLV v) := by
  solve_pure_exec
/-- Rocq: `pure_injrc`. -/
instance pure_injrc (v : val) :
    PureExec (Λ := con_prob_lang) True 1 (InjR <| Val v) (Val <| InjRV v) := by
  solve_pure_exec

/-- Rocq: `pure_beta`. -/
instance pure_beta (f x : binder) (erec : expr) (v1 v2 : val) [H : AsRecV v1 f x erec] :
    PureExec (Λ := con_prob_lang) True 1 (App (Val v1) (Val v2))
      (subst' x v2 (subst' f v1 erec)) := by
  obtain ⟨rfl⟩ := H
  solve_pure_exec

/-- Rocq: `pure_unop` (an instance in Rocq). In Lean this cannot be an instance: `v'` only
occurs in `outParam` arguments and is hence never determined by instance search. The
instance `pure_unop_eval` below is used instead. -/
theorem pure_unop (op : un_op) (v v' : val) :
    PureExec (Λ := con_prob_lang) (un_op_eval op v = some v') 1 (UnOp op (Val v)) (Val v') := by
  solve_pure_exec

/-- The instance form of `pure_unop` (not in Rocq): the result value is computed,
`(un_op_eval op v).getD v`, and the side condition is `(un_op_eval op v).isSome`. For closed
`op` and `v` both reduce by `simp [un_op_eval]` / `decide`. -/
instance pure_unop_eval (op : un_op) (v : val) :
    PureExec (Λ := con_prob_lang) ((un_op_eval op v).isSome = true) 1 (UnOp op (Val v))
      (Val ((un_op_eval op v).getD v)) := by
  refine ⟨fun h => (pure_unop op v _).pure_exec ?_⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h
  simp [hw]

/-- Rocq: `pure_binop` (an instance in Rocq, with cost `10`). In Lean this cannot be an instance
(see `pure_unop`); the instance `pure_binop_eval` below is used instead. -/
theorem pure_binop (op : bin_op) (v1 v2 v' : val) :
    PureExec (Λ := con_prob_lang) (bin_op_eval op v1 v2 = some v') 1
      (BinOp op (Val v1) (Val v2)) (Val v') := by
  solve_pure_exec

/-- The instance form of `pure_binop` (not in Rocq): the result value is computed,
`(bin_op_eval op v1 v2).getD v1`, and the side condition is `(bin_op_eval op v1 v2).isSome`. -/
instance pure_binop_eval (op : bin_op) (v1 v2 : val) :
    PureExec (Λ := con_prob_lang) ((bin_op_eval op v1 v2).isSome = true) 1
      (BinOp op (Val v1) (Val v2)) (Val ((bin_op_eval op v1 v2).getD v1)) := by
  refine ⟨fun h => (pure_binop op v1 v2 _).pure_exec ?_⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h
  simp [hw]

/-- Relates the computed form of `pure_unop_eval` to the Rocq form of `pure_unop` (not in Rocq):
the side condition holds with result `v'` iff `un_op_eval op v = some v'`. -/
theorem pure_unop_eval_iff (op : un_op) (v v' : val) :
    ((un_op_eval op v).isSome = true ∧ (un_op_eval op v).getD v = v') ↔
      un_op_eval op v = some v' := by
  cases un_op_eval op v <;> simp

/-- Relates the computed form of `pure_binop_eval` to the Rocq form of `pure_binop` (not in
Rocq): the side condition holds with result `v'` iff `bin_op_eval op v1 v2 = some v'`. -/
theorem pure_binop_eval_iff (op : bin_op) (v1 v2 v' : val) :
    ((bin_op_eval op v1 v2).isSome = true ∧ (bin_op_eval op v1 v2).getD v1 = v') ↔
      bin_op_eval op v1 v2 = some v' := by
  cases bin_op_eval op v1 v2 <;> simp

/-- Rocq: `pure_eqop`. Higher priority than the generic `pure_binop_eval` (Rocq: lower cost
than `pure_binop`). -/
instance (priority := default + 10) pure_eqop (v1 v2 : val) :
    PureExec (Λ := con_prob_lang) (vals_compare_safe v1 v2) 1
      (BinOp EqOp (Val v1) (Val v2))
      (Val <| LitV <| LitBool <| decide (v1 = v2)) := by
  have h : vals_compare_safe v1 v2 →
      bin_op_eval EqOp v1 v2 = some (LitV <| LitBool <| decide (v1 = v2)) := by
    intro hc
    simp [bin_op_eval, hc]
  exact ⟨fun hc => (pure_binop EqOp v1 v2 _).pure_exec (h hc)⟩

/-- Rocq: `pure_if_true`. -/
instance pure_if_true (e1 e2 : expr) :
    PureExec (Λ := con_prob_lang) True 1 (If (Val <| LitV <| LitBool true) e1 e2) e1 := by
  solve_pure_exec
/-- Rocq: `pure_if_false`. -/
instance pure_if_false (e1 e2 : expr) :
    PureExec (Λ := con_prob_lang) True 1 (If (Val <| LitV <| LitBool false) e1 e2) e2 := by
  solve_pure_exec

/-- Rocq: `pure_fst`. -/
instance pure_fst (v1 v2 : val) :
    PureExec (Λ := con_prob_lang) True 1 (Fst (Val <| PairV v1 v2)) (Val v1) := by
  solve_pure_exec
/-- Rocq: `pure_snd`. -/
instance pure_snd (v1 v2 : val) :
    PureExec (Λ := con_prob_lang) True 1 (Snd (Val <| PairV v1 v2)) (Val v2) := by
  solve_pure_exec

/-- Rocq: `pure_case_inl`. -/
instance pure_case_inl (v : val) (e1 e2 : expr) :
    PureExec (Λ := con_prob_lang) True 1 (Case (Val <| InjLV v) e1 e2) (App e1 (Val v)) := by
  solve_pure_exec
/-- Rocq: `pure_case_inr`. -/
instance pure_case_inr (v : val) (e1 e2 : expr) :
    PureExec (Λ := con_prob_lang) True 1 (Case (Val <| InjRV v) e1 e2) (App e2 (Val v)) := by
  solve_pure_exec

/-- Rocq: `pure_tick`. -/
instance pure_tick (z : ℤ) :
    PureExec (Λ := con_prob_lang) True 1 (Tick (Val (LitV (LitInt z)))) (Val (LitV LitUnit)) := by
  solve_pure_exec

end pure_exec

/-! ## Tests -/

section test

/-! Programs parse (and elaborate to the expected constructor terms). -/

example : cpl(λ x, x + #1) =
    Rec BAnon (BNamed "x") (BinOp PlusOp (Var "x") (Val (LitV (LitInt 1)))) := rfl
example : cpl((#1, #2, #3)) =
    Pair (Pair (Val (LitV (LitInt 1))) (Val (LitV (LitInt 2)))) (Val (LitV (LitInt 3))) := rfl
example : cpl(let x := ref(#0); x ← !x + #1; !x) =
    Let (BNamed "x") (Alloc (Val (LitV (LitInt 0))))
      (Seq (Store (Var "x") (BinOp PlusOp (Load (Var "x")) (Val (LitV (LitInt 1)))))
        (Load (Var "x"))) := rfl
example : cpl(let (a, b) := #1; a) =
    Let (BNamed "b") (Val (LitV (LitInt 1)))
      (Let (BNamed "a") (Fst (Var "b")) (Let (BNamed "b") (Snd (Var "b")) (Var "a"))) := rfl
example : cpl(let (a, b, c) := #1; a) =
    Let (BNamed "a") (Val (LitV (LitInt 1)))
      (Let (BNamed "b") (Snd (Fst (Var "a")))
        (Let (BNamed "c") (Snd (Var "a")) (Let (BNamed "a") (Fst (Fst (Var "a"))) (Var "a")))) :=
  rfl
example : cpl(let ("a", b) := #1; "a") = cpl(let (a, b) := #1; a) := rfl
example : cpl(let ("a", "b", c) := #1; a) = cpl(let (a, b, c) := #1; a) := rfl
example : cpl(let (a, ("b", c)) := #1; b) =
    Let (BNamed "a") (Val (LitV (LitInt 1)))
      (Let (BNamed "b") (Fst (Snd (Var "a")))
        (Let (BNamed "c") (Snd (Snd (Var "a"))) (Let (BNamed "a") (Fst (Var "a")) (Var "b")))) :=
  rfl
example (e : expr) : cpl(match &e with | none() => #0 | some(y) => y) =
    Match e BAnon (Val (LitV (LitInt 0))) (BNamed "y") (Var "y") := rfl
example : cpl(let α := alloc(#10); rand(α) #10) =
    Let (BNamed "α") (alloc (Val (LitV (LitInt 10))))
      (Rand (Val (LitV (LitInt 10))) (Var "α")) := rfl
example : cpl(rand(#10)) = Rand (Val (LitV (LitInt 10))) (Val (LitV LitUnit)) := rfl
example (l : Loc) : cpl(rand(#lbl(l)) #5) =
    Rand (Val (LitV (LitInt 5))) (Val (LitV (LitLbl l))) := rfl
example : cpl(skip) = Skip := rfl
example (e1 e2 e3 : expr) : cpl(cas(&e1, &e2, &e3)) = CAS e1 e2 e3 := rfl
example : cpl(tick(#1); fork(#())) =
    Seq (tick (Val (LitV (LitInt 1)))) (Fork (Val (LitV LitUnit))) := rfl
example : cpl("x" ≠ #(-1)) =
    UnOp NegOp (BinOp EqOp (Var "x") (Val (LitV (LitInt (-1))))) := rfl
example (e : expr) : cpl(let:m y := &e in some(y)) =
    Match e BAnon NONE (BNamed "y") (SOME (Var "y")) := rfl
example : cpl_val(λ x y, x) = RecV BAnon (BNamed "x") (Lam (BNamed "y") (Var "x")) := rfl
example : cpl(letrec f n := if n = #0 then #1 else n * f (n - #1) in f #5) =
    Let (BNamed "f")
      (Rec (BNamed "f") (BNamed "n")
        (If (BinOp EqOp (Var "n") (Val (LitV (LitInt 0)))) (Val (LitV (LitInt 1)))
          (BinOp MultOp (Var "n")
            (App (Var "f") (BinOp MinusOp (Var "n") (Val (LitV (LitInt 1))))))))
      (App (Var "f") (Val (LitV (LitInt 5)))) := rfl
example (e : expr) : cpl(while &e do skip end) =
    App (Rec (BNamed "loop") BAnon
      (If e (Seq Skip (App (Var "loop") (Val (LitV LitUnit)))) (Val (LitV LitUnit))))
      (Val (LitV LitUnit)) := rfl
/-- The coercions `val → expr`, `ℤ → base_lit`, `String → expr` and `expr → Funclass`. -/
example (v : val) (f : expr) :
    (f (v : expr) : expr) = App f (Val v) ∧ (LitV (3 : ℤ) : val) = LitV (LitInt 3) ∧
      (("x" : String) : expr) = Var "x" := ⟨rfl, rfl, rfl⟩

/-! `PureExec` instances resolve. -/

example : PureExec (Λ := con_prob_lang) True 1 cpl(fst(v((#1, #2)))) cpl(#1) := inferInstance
example : PureExec (Λ := con_prob_lang) True 1 cpl(if #true then #1 else #2) cpl(#1) :=
  inferInstance
example : PureExec (Λ := con_prob_lang) True 1 cpl(v(λ x, x + #1) #2) cpl(#2 + #1) :=
  inferInstance
example : PureExec (Λ := con_prob_lang) True 1 cpl(λ x, x) cpl(v(λ x, x)) := inferInstance
example : PureExec (Λ := con_prob_lang) True 1 cpl(tick(#3)) cpl(#()) := inferInstance
example : PureExec (Λ := con_prob_lang) True 1 cpl((#1, #2)) cpl(v((#1, #2))) := inferInstance
example (v : val) (e1 e2 : expr) :
    PureExec (Λ := con_prob_lang) True 1 (Case (Val (InjLV v)) e1 e2) (App e1 (Val v)) :=
  inferInstance
example : nsteps (pure_step (Λ := con_prob_lang)) 1 cpl(#1 = #1) cpl(#true) := by
  have h := (inferInstance : PureExec (Λ := con_prob_lang) _ _ cpl(#1 = #1) _).pure_exec
    (Or.inl trivial)
  simpa using h
example : nsteps (pure_step (Λ := con_prob_lang)) 1 cpl(#1 + #2) cpl(#3) := by
  have h := (inferInstance : PureExec (Λ := con_prob_lang) _ _ cpl(#1 + #2) _).pure_exec
    (by decide)
  simpa [bin_op_eval, bin_op_eval_int] using h
example : nsteps (pure_step (Λ := con_prob_lang)) 1 cpl(~#true) cpl(#false) := by
  have h := (inferInstance : PureExec (Λ := con_prob_lang) _ _ cpl(~#true) _).pure_exec
    (by decide)
  simpa [un_op_eval] using h

/-! `Atomic`, `IntoVal`, `AsVal` instances resolve. -/

example (l : Loc) : Atomic (Λ := con_prob_lang) .WeaklyAtomic cpl(!#l) := inferInstance
example (l : Loc) : Atomic (Λ := con_prob_lang) .StronglyAtomic cpl(rand(#lbl(l)) #3) :=
  inferInstance
example : Atomic (Λ := con_prob_lang) .StronglyAtomic cpl(ref(#3)) := inferInstance
example : Atomic (Λ := con_prob_lang) .StronglyAtomic Skip := inferInstance
example : IntoVal (Λ := con_prob_lang) cpl(#3) (LitV (LitInt 3)) := inferInstance
example : AsVal (Λ := con_prob_lang) cpl(#3) := inferInstance

/-! Tactics: `reshape_expr`, `solve_step`. -/

set_option linter.unusedTactic false in
example (σ : state) : reducible (Λ := con_prob_lang) cpl((#1, #2); #3) σ := by
  reshape_expr cpl((#1, #2); #3) as K e =>
    guard_expr e =ₛ cpl((#1, #2))
    rw [show cpl((#1, #2); #3) = fill K e from rfl]
    solve_red
example (σ : state) : head_step cpl(fst(v((#1, #2)))) σ (cpl(#1), σ, []) = 1 := by solve_step
example (σ : state) : 0 < head_step cpl(fst(v((#1, #2)))) σ (cpl(#1), σ, []) := by solve_step
example (σ : state) :
    prim_step (Λ := con_prob_lang) cpl(fst(v((#1, #2)))) σ (cpl(#1), σ, []) = 1 := by
  solve_step

end test

end con_prob_lang
end ConProbLang

end
