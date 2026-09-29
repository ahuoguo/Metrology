module

public import Metrology.ConProbLang.Lang
public import Lean.PrettyPrinter.Parenthesizer

/-!
# Notation for `con_prob_lang` programs

Ported from clutch/theories/con_prob_lang/notation.v

The design mirrors iris-lean's `Iris/HeapLang/Notation.lean`: programs are written inside the
term-level embedding `cpl(...)` (iris-lean: `hl(...)`), values inside `cpl_val(...)` and
binders inside `cpl_binder(...)`. The notation elaborates by macros directly to the constructors
of `ConProbLang.con_prob_lang.expr`/`val`, so instances (`PureExec`, `Atomic`, ...) and lemmas
stated with constructors apply to programs written with the notation. Delaborators print the
constructors back in the notation.

## Rocq → Lean mapping

Coercions (global instances, as the Rocq `Coercion`s):
* `LitInt : Z >-> base_lit`, `LitBool : bool >-> base_lit`, `LitLoc : loc >-> base_lit` are
  `Coe ℤ base_lit`, `Coe Bool base_lit`, `Coe Loc base_lit` (plus `Coe ℕ base_lit` and
  `Coe Unit base_lit`, as in iris-lean, for convenience).
* `Val : val >-> expr`, `Var : string >-> expr`, `App : expr >-> Funclass` are
  `Coe val expr`, `Coe String expr`, `CoeFun expr (fun _ => expr → expr)`.

Derived forms (Rocq `Notation ... (only parsing)`), here `abbrev`s in `ConProbLang.con_prob_lang`
(so they unfold at reducible transparency, e.g. during instance search):
`Lam`, `Let`, `Seq`, `LamV`, `LetCtx`, `SeqCtx`, `Alloc`, `Match`, `CAS`, `Skip`, `NONE`,
`NONEV`, `SOME`, `SOMEV`, `alloc` (= `AllocTape`), `tick` (= `Tick`).
Note that `Seq` shadows the core class `Seq` when `ConProbLang.con_prob_lang` is opened.

Program notation (inside `cpl(...)`; Rocq notation on the right):
| Lean                                   | Rocq                                        |
|----------------------------------------|---------------------------------------------|
| `x` (an identifier), `"x"`             | `"x"` (a `Var`)                             |
| `&t`                                   | a Lean term `t` (antiquotation)             |
| `#t`, `#3`, `#()`, `#true`, `#l`       | `#t`                                        |
| `#lbl(α)`                              | `#lbl:α`                                    |
| `v(w)` (with `w` in value syntax)      | `Val w`                                     |
| `e1 e2`                                | `e1 e2`                                     |
| `λ x y, e`, `rec f x y := e`           | `λ: x y, e`, `rec: f x y := e`              |
| `x`, `_`, `"x"`, `<>`, `&b` (binders)   | `"x"`, `<>`                                 |
| `let x := e1; e2`, `let x := e1 in e2` | `let: x := e1 in e2`                        |
| `e1; e2`                               | `e1 ;; e2`                                  |
| `let (x1, x2, ..) := e1; e2`           | `let, (x1, x2, ..) := e1 in e2`             |
| `let (x1, (x2, x3)) := e1; e2`         | `let, (x1, (x2, x3)) := e1 in e2`           |
| `(e1, e2, e3)` (LEFT-nested pairs)     | `(e1, e2, e3)`                              |
| `fst(e)`, `snd(e)`                     | `Fst e`, `Snd e`                            |
| `injl(e)`, `injr(e)`, `none()`, `some(e)` | `InjL e`, `InjR e`, `NONE`, `SOME e`     |
| `match e with \| injl(x) => e1 \| injr(y) => e2` | `match: e with InjL x => e1 \| InjR y => e2 end` |
| `match e with \| none() => e1 \| some(x) => e2` | `match: e with NONE => e1 \| SOME x => e2 end` |
| `if e0 then e1 else e2`                | `if: e0 then e1 else e2`                    |
| `e1 + e2`, `-`, `*`, `/`, `%`          | `+`, `-`, `*`, `` `quot` ``, `` `rem` ``    |
| `&&&`, `\|\|\|`, `^^^`, `<<<`, `>>>`   | `` `and` ``, `` `or` ``, (xor), `≪`, `≫`    |
| `e1 +ₗ e2`, `≤`/`<=`, `<`, `=`, `≠`    | `+ₗ`, `≤`, `<`, `=`, `≠`                    |
| `~e`, `-e`                             | `~ e`, `- e`                                |
| `e1 && e2`, `e1 \|\| e2`               | `e1 && e2`, `e1 \|\| e2` (short-circuit)    |
| `allocn(e1, e2)`, `ref(e)`, `!e`       | `AllocN e1 e2`, `ref e`, `! e`              |
| `e1 ← e2`, `e1 <- e2`                  | `e1 <- e2`                                  |
| `cmpXchg(e0,e1,e2)`, `cas(..)`, `xchg(e1,e2)`, `faa(e1,e2)` | `CmpXchg`, `CAS`, `Xchg`, `FAA` |
| `fork(e)`                              | `Fork e`                                    |
| `alloc(e)`                             | `alloc e` (`AllocTape`)                     |
| `rand(e)`                              | `rand e` (`Rand e #()`)                     |
| `rand(α) e`                            | `rand(α) e` (`Rand e α`)                    |
| `tick(e)`                              | `tick e`                                    |
| `skip`                                 | `Skip`                                      |
| `let:m x := e1 in e2`                  | `let:m x := e1 in e2`                       |
| `assert(e1) ;;; e2`                    | `assert e1 ;;; e2`                          |
| `while e1 do e2 end`                   | `while e1 do e2 end`                        |
| `letrec f x y := e1 in e2`             | `letrec: f x y := e1 in e2`                 |
| `_`                                    | a hole                                      |

Values (inside `cpl_val(...)`): `&t`, `#t`, `#lbl(α)`, `(v1, v2, ..)` (left-nested),
`injl(v)`, `injr(v)`, `none()`, `some(v)`, `λ x y, e`, `rec f x y := e`.

Differences from Rocq:
* Rocq tuples `(e1, e2, e3)` are LEFT-nested (`Pair (Pair e1 e2) e3`); this is kept (iris-lean's
  `hl` tuples are right-nested).
* Variables are identifiers (as in iris-lean) or string literals (as in Rocq); Lean terms must
  be escaped with `&`.
* Scopes (`%E`, `%V`, `%binder`) are replaced by the three embeddings.
* Rocq printing boxes/formats are replaced by delaborators (as in iris-lean).
* `skip` elaborates to the constructor form `v(λ _, #()) #()` of `Skip` (equal by `rfl`).
* `rand(α) e` takes its second argument at level 70 (as in Rocq); beware that
  `rand(e1) -e2` hence parses as the labelled `Rand (-e2) e1`.
* `#t` elaborates `t` against `base_lit` (through the coercions); numerals `#3` and negated
  numerals `#(-3)` are special-cased to `LitInt`.
* Rocq's `≪`/`≫`, `` `quot` ``, `` `rem` ``, `` `and` ``, `` `or` `` are written as in iris-lean
  (`<<<`/`>>>`, `/`, `%`, `&&&`, `|||`).
-/

@[expose] public section

namespace ConProbLang
namespace con_prob_lang

/-! ## Coercions -/

/-- Rocq: `Coercion LitInt : Z >-> base_lit`. -/
instance : Coe ℤ base_lit := ⟨LitInt⟩
/-- As in iris-lean (not in Rocq). -/
instance : Coe ℕ base_lit := ⟨fun n => LitInt n⟩
/-- Rocq: `Coercion LitBool : bool >-> base_lit`. -/
instance : Coe Bool base_lit := ⟨LitBool⟩
/-- Rocq: `Coercion LitLoc : loc >-> base_lit`. -/
instance : Coe Loc base_lit := ⟨LitLoc⟩
/-- As in iris-lean (not in Rocq): `()` is `LitUnit`. -/
instance : Coe Unit base_lit := ⟨fun _ => LitUnit⟩
/-- Rocq: `Coercion Val : val >-> expr`. -/
instance : Coe val expr := ⟨Val⟩
/-- Rocq: `Coercion Var : string >-> expr`. -/
instance : Coe String expr := ⟨Var⟩
/-- Rocq: `Coercion App : expr >-> Funclass`. -/
instance : CoeFun expr (fun _ => expr → expr) := ⟨App⟩

attribute [coe] base_lit.LitInt base_lit.LitBool base_lit.LitLoc

/-! ## Derived forms -/

/-- Rocq: `Lam`. -/
abbrev Lam (x : binder) (e : expr) : expr := Rec BAnon x e
/-- Rocq: `Let`. -/
abbrev Let (x : binder) (e1 e2 : expr) : expr := App (Lam x e2) e1
/-- Rocq: `Seq`. -/
abbrev Seq (e1 e2 : expr) : expr := Let BAnon e1 e2
/-- Rocq: `LamV`. -/
abbrev LamV (x : binder) (e : expr) : val := RecV BAnon x e
/-- Rocq: `LetCtx`. -/
abbrev LetCtx (x : binder) (e2 : expr) : ectx_item := AppRCtx (Val (LamV x e2))
/-- Rocq: `SeqCtx`. -/
abbrev SeqCtx (e2 : expr) : ectx_item := LetCtx BAnon e2
/-- Rocq: `Alloc`. -/
abbrev Alloc (e : expr) : expr := AllocN (Val <| LitV <| LitInt 1) e
/-- Rocq: `Match`. -/
abbrev Match (e0 : expr) (x1 : binder) (e1 : expr) (x2 : binder) (e2 : expr) : expr :=
  Case e0 (Lam x1 e1) (Lam x2 e2)
/-- Rocq: `CAS`. Compare-and-set (CAS) returns just a boolean indicating success or failure. -/
abbrev CAS (l e1 e2 : expr) : expr := Snd (CmpXchg l e1 e2)
/-- Rocq: `Skip`. Skip should be atomic, we sometimes open invariants around it. Hence, we need
to explicitly use `LamV` instead of e.g., `Seq`. -/
abbrev Skip : expr := App (Val <| LamV BAnon (Val <| LitV LitUnit)) (Val <| LitV LitUnit)
/-- Rocq: `NONE`. -/
abbrev NONE : expr := InjL (Val <| LitV LitUnit)
/-- Rocq: `NONEV`. -/
abbrev NONEV : val := InjLV (LitV LitUnit)
/-- Rocq: `SOME`. -/
abbrev SOME (x : expr) : expr := InjR x
/-- Rocq: `SOMEV`. -/
abbrev SOMEV (x : val) : val := InjRV x
/-- Rocq: `alloc` (notation for `AllocTape`). -/
abbrev alloc (e : expr) : expr := AllocTape e
/-- Rocq: `tick` (notation for `Tick`). -/
abbrev tick (e : expr) : expr := Tick e

end con_prob_lang
end ConProbLang

end

public meta section

namespace ConProbLang
namespace con_prob_lang

open Lean Lean.PrettyPrinter Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr Elab Parser

set_option linter.overlappingInstances false

declare_syntax_cat cpl_exp
declare_syntax_cat cpl_binder
declare_syntax_cat cpl_match_arm
declare_syntax_cat cpl_val

/-- embedding `con_prob_lang` expressions into terms -/
syntax:max "cpl(" cpl_exp ")" : term
syntax:min "cpl% " cpl_exp:min : term
macro_rules
  | `(cpl% $t) => `(cpl($t))
/-- embedding `con_prob_lang` binders into terms -/
syntax:max "cpl_binder(" cpl_binder ")" : term
/-- embedding `con_prob_lang` values into terms -/
syntax:max "cpl_val(" cpl_val ")" : term
syntax:min "cpl_val% " cpl_val:min : term
macro_rules
  | `(cpl_val% $t) => `(cpl_val($t))

/-! ### Binders -/

/-- escaping -/
syntax:max "&" term:max : cpl_binder
syntax:max binderIdent : cpl_binder
/-- Rocq-style string binders -/
syntax:max str : cpl_binder
/-- Rocq-style anonymous binder `<>` -/
syntax:max "<>" : cpl_binder

/-! ### Values -/

/-- escaping -/
syntax:max "&" term:max : cpl_val
/-- embedding literals -/
syntax:max "#" term:max : cpl_val
/-- tape labels (Rocq: `#lbl:α`) -/
syntax:max "#lbl(" term ")" : cpl_val
/-- (left-nested) pairs -/
syntax:max "(" cpl_val ", " cpl_val,+ ")" : cpl_val
/-- parenthesis -/
syntax:max "(" cpl_val ")" : cpl_val
/-- injL -/
syntax:100 "injl(" cpl_val ")" : cpl_val
/-- injR -/
syntax:100 "injr(" cpl_val ")" : cpl_val
/-- none and some -/
syntax:100 "none()" : cpl_val
syntax:100 "some(" cpl_val ")" : cpl_val

/-! ### Expressions -/

/-- parenthesis -/
syntax:max "(" cpl_exp ")" : cpl_exp
/-- embedding values -/
syntax:max "v(" cpl_val ")" : cpl_exp
/-- escaping -/
syntax:max "&" term:max : cpl_exp
/-- embedding literals -/
syntax:max "#" term:max : cpl_exp
/-- tape labels (Rocq: `#lbl:α`) -/
syntax:max "#lbl(" term ")" : cpl_exp
/-- variables -/
syntax:max ident : cpl_exp
/-- Rocq-style string variables -/
syntax:max str : cpl_exp
/-- `Skip` -/
syntax:max "skip" : cpl_exp
-- levels are taken from iris-lean's `HeapLang/Notation.lean`
/-- addition -/
syntax:65 cpl_exp:66 " + " cpl_exp:65 : cpl_exp
/-- offset -/
syntax:65 cpl_exp:66 " +ₗ " cpl_exp:65 : cpl_exp
/-- subtraction -/
syntax:65 cpl_exp:66 " - " cpl_exp:65 : cpl_exp
/-- multiplication -/
syntax:70 cpl_exp:71 " * " cpl_exp:70 : cpl_exp
/-- division (Rocq: `quot`) -/
syntax:70 cpl_exp:71 " / " cpl_exp:70 : cpl_exp
/-- remainder (Rocq: `rem`) -/
syntax:70 cpl_exp:71 " % " cpl_exp:70 : cpl_exp
/-- and -/
syntax:60 cpl_exp:61 " &&& " cpl_exp:60 : cpl_exp
/-- or -/
syntax:55 cpl_exp:56 " ||| " cpl_exp:55 : cpl_exp
/-- xor -/
syntax:58 cpl_exp:59 " ^^^ " cpl_exp:58 : cpl_exp
/-- shiftl -/
syntax:75 cpl_exp:76 " <<< " cpl_exp:75 : cpl_exp
/-- shiftr -/
syntax:75 cpl_exp:76 " >>> " cpl_exp:75 : cpl_exp
/-- le -/
syntax:50 cpl_exp:50 " <= " cpl_exp:50 : cpl_exp
syntax:50 cpl_exp:50 " ≤ " cpl_exp:50 : cpl_exp
/-- lt -/
syntax:50 cpl_exp:50 " < " cpl_exp:50 : cpl_exp
/-- equality -/
syntax:50 cpl_exp:50 " = " cpl_exp:50 : cpl_exp
/-- disequality -/
syntax:50 cpl_exp:50 " ≠ " cpl_exp:50 : cpl_exp

/-- short-circuit conjunction and disjunction -/
syntax:35 cpl_exp:36 " && " cpl_exp:35 : cpl_exp
syntax:30 cpl_exp:31 " || " cpl_exp:30 : cpl_exp

/-- neg -/
syntax:100 "~" cpl_exp:100 : cpl_exp
/-- minus -/
syntax:75 "-" cpl_exp:75 : cpl_exp

/-- if -/
syntax:10 "if " cpl_exp:10 " then " cpl_exp:10 " else " cpl_exp:10 : cpl_exp

/-- application -/
syntax:100 cpl_exp:100 colGt ppSpace cpl_exp:101 : cpl_exp
/-- let -/
syntax:10 "let " cpl_binder " := " cpl_exp:10 "; " cpl_exp:1 : cpl_exp
syntax:10 "let " cpl_binder " := " cpl_exp:10 " in " cpl_exp:1 : cpl_exp
/-- destructuring let (Rocq: `let,`) -/
syntax:10 "let " "(" ident ", " ident,+ ")" " := " cpl_exp:10 "; " cpl_exp:1 : cpl_exp
syntax:10 "let " "(" ident ", " "(" ident ", " ident ")" ")" " := " cpl_exp:10 "; "
  cpl_exp:1 : cpl_exp
/-- sequencing -/
syntax:5 cpl_exp:6 "; " cpl_exp:5 : cpl_exp
/-- lambda -/
syntax:10 "λ " cpl_binder+ ", " cpl_exp:1 : cpl_exp
/-- lambda -/
syntax:10 "λ " cpl_binder+ ", " cpl_exp:1 : cpl_val
/-- recursive function -/
syntax:10 "rec " cpl_binder ppSpace cpl_binder+ " := " cpl_exp:1 : cpl_exp
/-- recursive function -/
syntax:10 "rec " cpl_binder ppSpace cpl_binder+ " := " cpl_exp:1 : cpl_val
/-- recursive let (Rocq: `letrec:`) -/
syntax:10 "letrec " cpl_binder ppSpace cpl_binder+ " := " cpl_exp:10 " in " cpl_exp:1 : cpl_exp

/-- (left-nested) pairs -/
syntax:max "(" cpl_exp ", " cpl_exp,+ ")" : cpl_exp
/-- fst -/
syntax:100 "fst(" cpl_exp ")" : cpl_exp
/-- snd -/
syntax:100 "snd(" cpl_exp ")" : cpl_exp

/-- injL -/
syntax:100 "injl(" cpl_exp ")" : cpl_exp
/-- injR -/
syntax:100 "injr(" cpl_exp ")" : cpl_exp

/-- none and some -/
syntax:100 "none()" : cpl_exp
syntax:100 "some(" cpl_exp ")" : cpl_exp

/-- match -/
syntax:100 "match " cpl_exp:5 " with"
  " | " cpl_match_arm " => " cpl_exp:5
  " | " cpl_match_arm " => " cpl_exp:5 : cpl_exp

syntax "injl(" cpl_binder ")" : cpl_match_arm
syntax "injr(" cpl_binder ")" : cpl_match_arm
syntax "some(" cpl_binder ")" : cpl_match_arm
syntax "none()" : cpl_match_arm

/-- option monad (Rocq: `let:m`) -/
syntax:10 "let:m " cpl_binder " := " cpl_exp:10 " in " cpl_exp:1 : cpl_exp
/-- `assert e1 ;;; e2` errors out (returns `NONE`) if `e1` evaluates to false. -/
syntax:10 "assert(" cpl_exp ")" " ;;; " cpl_exp:10 : cpl_exp
/-- while loops -/
syntax:100 "while " cpl_exp " do " cpl_exp " end" : cpl_exp

/-- heap operations -/
syntax:100 "allocn(" cpl_exp ", " cpl_exp ")" : cpl_exp
syntax:100 "ref(" cpl_exp ")" : cpl_exp
syntax:100 "!" cpl_exp:100 : cpl_exp
syntax:15 cpl_exp:16 " ← " cpl_exp:15 : cpl_exp
syntax:15 cpl_exp:16 " <- " cpl_exp:15 : cpl_exp
syntax:100 "cmpXchg(" cpl_exp ", " cpl_exp ", " cpl_exp ")" : cpl_exp
syntax:100 "cas(" cpl_exp ", " cpl_exp ", " cpl_exp ")" : cpl_exp
syntax:100 "xchg(" cpl_exp ", " cpl_exp ")" : cpl_exp
syntax:100 "faa(" cpl_exp ", " cpl_exp ")" : cpl_exp

/-- fork -/
syntax:100 "fork(" cpl_exp ")" : cpl_exp

/-- probabilistic operations: tape allocation, (labelled) sampling -/
syntax:100 "alloc(" cpl_exp ")" : cpl_exp
/-- `rand(e)` is `Rand e #()`; `rand(α) e` is `Rand e α` (Rocq: `rand e`, `rand(α) e`). -/
syntax:70 "rand(" cpl_exp ")" (ppSpace cpl_exp:70)? : cpl_exp

/-- tick -/
syntax:100 "tick(" cpl_exp ")" : cpl_exp

/-- holes -/
syntax "_" : cpl_exp

open Lean.PrettyPrinter.Parenthesizer in
@[category_parenthesizer cpl_exp]
def cpl_exp.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `cpl_exp false (fun stx => Unhygienic.run `(cpl_exp|($(⟨stx⟩)))) prec <|
    parenthesizeCategoryCore `cpl_exp prec

open Lean.PrettyPrinter.Parenthesizer in
@[category_parenthesizer cpl_val]
def cpl_val.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `cpl_val false (fun stx => Unhygienic.run `(cpl_val|($(⟨stx⟩)))) prec <|
    parenthesizeCategoryCore `cpl_val prec

partial def unpackCPLExp [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `cpl_exp)
  | `(cpl($e)) => `(cpl_exp|$e)
  | `($t) => `(cpl_exp|&$t)

partial def unpackCPLVal [Monad m] [MonadRef m] [MonadQuotation m] : Term → m (TSyntax `cpl_val)
  | `(cpl_val($e)) => `(cpl_val|$e)
  | `($t) => `(cpl_val|&$t)

partial def unpackCPLBinder [Monad m] [MonadRef m] [MonadQuotation m] :
    Term → m (TSyntax `cpl_binder)
  | `(cpl_binder($e)) => `(cpl_binder|$e)
  | `($t) => `(cpl_binder|&$t)

/-- The object-level name of an identifier (macro scopes erased). -/
def identStr (i : Ident) : StrLit := Syntax.mkStrLit i.getId.eraseMacroScopes.toString

/-- elaborating binders -/
macro_rules
  | `(cpl_binder(_)) => `(ConProbLang.binder.BAnon)
  | `(cpl_binder(<>)) => `(ConProbLang.binder.BAnon)
  | `(cpl_binder($i:ident)) => `(ConProbLang.binder.BNamed $(identStr i))
  | `(cpl_binder($s:str)) => `(ConProbLang.binder.BNamed $s)
  | `(cpl_binder(&$t)) => `($t)

/-- elaborating values -/
macro_rules
  | `(cpl_val(& $t)) => pure t
  | `(cpl_val(($v))) => `(cpl_val($v))
  | `(cpl_val(# ())) => `(ConProbLang.con_prob_lang.val.LitV ConProbLang.con_prob_lang.base_lit.LitUnit)
  | `(cpl_val(# (- $n:num))) =>
    `(ConProbLang.con_prob_lang.val.LitV (ConProbLang.con_prob_lang.base_lit.LitInt (- $n)))
  | `(cpl_val(# $n:num)) =>
    `(ConProbLang.con_prob_lang.val.LitV (ConProbLang.con_prob_lang.base_lit.LitInt $n))
  | `(cpl_val(# $e)) => `(ConProbLang.con_prob_lang.val.LitV $e)
  | `(cpl_val(#lbl($e))) =>
    `(ConProbLang.con_prob_lang.val.LitV (ConProbLang.con_prob_lang.base_lit.LitLbl $e))
  | `(cpl_val(rec $f $x := $e)) =>
    `(ConProbLang.con_prob_lang.val.RecV cpl_binder($f) cpl_binder($x) cpl($e))
  | `(cpl_val(rec $f $x $xs* := $e)) => `(cpl_val(rec $f $x := λ $xs*, $e))
  | `(cpl_val(λ $xs*, $e)) => `(cpl_val(rec _ $xs* := $e))
  | `(cpl_val(($e1, $e2))) => `(ConProbLang.con_prob_lang.val.PairV cpl_val($e1) cpl_val($e2))
  | `(cpl_val(($e1, $e2, $es,*))) => do
    let mut acc ← `(cpl_val|($e1, $e2))
    for e in es.getElems do acc ← `(cpl_val|($acc, $e))
    `(cpl_val($acc))
  | `(cpl_val(injl($e1))) => `(ConProbLang.con_prob_lang.val.InjLV cpl_val($e1))
  | `(cpl_val(injr($e1))) => `(ConProbLang.con_prob_lang.val.InjRV cpl_val($e1))
  | `(cpl_val(none())) => `(cpl_val(injl(#())))
  | `(cpl_val(some($e))) => `(cpl_val(injr($e)))

/-- `fst` iterated `n` times on `e` (used for the destructuring `let`). -/
def iterFst (n : Nat) (e : TSyntax `cpl_exp) : MacroM (TSyntax `cpl_exp) :=
  match n with
  | 0 => pure e
  | n + 1 => do iterFst n (← `(cpl_exp| fst($e)))

/-- elaborating expressions -/
macro_rules
  | `(cpl(($e))) => `(cpl($e))
  | `(cpl(_)) => `(_)
  | `(cpl(&$t)) => pure t
  | `(cpl(v($e))) => `(ConProbLang.con_prob_lang.expr.Val cpl_val($e))
  | `(cpl(# $e)) => `(cpl(v(# $e)))
  | `(cpl(#lbl($e))) => `(cpl(v(#lbl($e))))
  | `(cpl($i:ident)) => `(ConProbLang.con_prob_lang.expr.Var $(identStr i))
  | `(cpl($s:str)) => `(ConProbLang.con_prob_lang.expr.Var $s)
  | `(cpl(skip)) => `(cpl(v(λ _, #()) #()))
  | `(cpl($e1 + $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.PlusOp cpl($e1) cpl($e2))
  | `(cpl($e1 +ₗ $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.OffsetOp cpl($e1) cpl($e2))
  | `(cpl($e1 - $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.MinusOp cpl($e1) cpl($e2))
  | `(cpl($e1 * $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.MultOp cpl($e1) cpl($e2))
  | `(cpl($e1 / $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.QuotOp cpl($e1) cpl($e2))
  | `(cpl($e1 % $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.RemOp cpl($e1) cpl($e2))
  | `(cpl($e1 &&& $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.AndOp cpl($e1) cpl($e2))
  | `(cpl($e1 ||| $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.OrOp cpl($e1) cpl($e2))
  | `(cpl($e1 ^^^ $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.XorOp cpl($e1) cpl($e2))
  | `(cpl($e1 <<< $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.ShiftLOp cpl($e1) cpl($e2))
  | `(cpl($e1 >>> $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.ShiftROp cpl($e1) cpl($e2))
  | `(cpl($e1 <= $e2)) => `(cpl($e1 ≤ $e2))
  | `(cpl($e1 ≤ $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.LeOp cpl($e1) cpl($e2))
  | `(cpl($e1 < $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.LtOp cpl($e1) cpl($e2))
  | `(cpl($e1 = $e2)) =>
    `(ConProbLang.con_prob_lang.expr.BinOp ConProbLang.con_prob_lang.bin_op.EqOp cpl($e1) cpl($e2))
  | `(cpl($e1 ≠ $e2)) => `(cpl(~($e1 = $e2)))
  | `(cpl($e1 && $e2)) => `(cpl(if $e1 then $e2 else #false))
  | `(cpl($e1 || $e2)) => `(cpl(if $e1 then #true else $e2))
  | `(cpl(~$e1)) =>
    `(ConProbLang.con_prob_lang.expr.UnOp ConProbLang.con_prob_lang.un_op.NegOp cpl($e1))
  | `(cpl(-$e1)) =>
    `(ConProbLang.con_prob_lang.expr.UnOp ConProbLang.con_prob_lang.un_op.MinusUnOp cpl($e1))
  | `(cpl(if $e1 then $e2 else $e3)) =>
    `(ConProbLang.con_prob_lang.expr.If cpl($e1) cpl($e2) cpl($e3))
  | `(cpl($e1 $e2)) => `(ConProbLang.con_prob_lang.expr.App cpl($e1) cpl($e2))
  | `(cpl(rec $f $x := $e)) =>
    `(ConProbLang.con_prob_lang.expr.Rec cpl_binder($f) cpl_binder($x) cpl($e))
  | `(cpl(rec $f $x $xs* := $e)) => `(cpl(rec $f $x := λ $xs*, $e))
  | `(cpl(λ $xs*, $e)) => `(cpl(rec _ $xs* := $e))
  | `(cpl(letrec $f $xs* := $e1 in $e2)) => `(cpl(let $f := (rec $f $xs* := $e1); $e2))
  | `(cpl($e1; $e2)) => `(cpl(let _ := $e1; $e2))
  | `(cpl(let $i := $e1 in $e2)) => `(cpl(let $i := $e1; $e2))
  | `(cpl(let $i := $e1; $e2)) => `(cpl((λ $i, $e2) $e1))
  | `(cpl(let ($x1, $x2) := $e1; $e2)) =>
    `(cpl(let $x2:ident := $e1; let $x1:ident := fst($x2:ident); let $x2:ident := snd($x2:ident); $e2))
  | `(cpl(let ($x1, ($x2, $x3)) := $e1; $e2)) =>
    `(cpl(let $x1:ident := $e1; let $x2:ident := fst(snd($x1:ident)); let $x3:ident := snd(snd($x1:ident));
          let $x1:ident := fst($x1:ident); $e2))
  | `(cpl(let ($x1, $xs,*) := $e1; $e2)) => do
    -- `(x1, .., xn)` is left-nested: `xi` (i ≥ 2) is `snd (fst^(n-i) x1)`, `x1` is
    -- `fst^(n-1) x1`.
    let xs := xs.getElems
    let n := xs.size + 1
    let x1e ← `(cpl_exp| $x1:ident)
    let mut body ← `(cpl_exp| let $x1:ident := $(← iterFst (n - 1) x1e); $e2)
    for i in [0:xs.size] do
      let j := xs.size - 1 - i
      let xj := xs[j]!
      -- `xj` is component `j + 2`
      let proj ← iterFst (n - (j + 2)) x1e
      body ← `(cpl_exp| let $xj:ident := snd($proj); $body)
    `(cpl(let $x1:ident := $e1; $body))
  | `(cpl(($e1, $e2))) => `(ConProbLang.con_prob_lang.expr.Pair cpl($e1) cpl($e2))
  | `(cpl(($e1, $e2, $es,*))) => do
    let mut acc ← `(cpl_exp|($e1, $e2))
    for e in es.getElems do acc ← `(cpl_exp|($acc, $e))
    `(cpl($acc))
  | `(cpl(fst($e1))) => `(ConProbLang.con_prob_lang.expr.Fst cpl($e1))
  | `(cpl(snd($e1))) => `(ConProbLang.con_prob_lang.expr.Snd cpl($e1))
  | `(cpl(match $e1 with | injl($i2) => $e2 | injr($i3) => $e3)) =>
    `(ConProbLang.con_prob_lang.expr.Case cpl($e1) cpl(λ $i2, $e2) cpl(λ $i3, $e3))
  | `(cpl(match $e1 with | injr($i2) => $e2 | injl($i3) => $e3)) =>
    `(cpl(match $e1 with | injl($i3) => $e3 | injr($i2) => $e2))
  | `(cpl(match $e1 with | some($i2) => $e2 | none() => $e3)) =>
    `(cpl(match $e1 with | injr($i2) => $e2 | injl(_) => $e3))
  | `(cpl(match $e1 with | none() => $e2 | some($i3) => $e3)) =>
    `(cpl(match $e1 with | injl(_) => $e2 | injr($i3) => $e3))
  | `(cpl(injl($e1))) => `(ConProbLang.con_prob_lang.expr.InjL cpl($e1))
  | `(cpl(injr($e1))) => `(ConProbLang.con_prob_lang.expr.InjR cpl($e1))
  | `(cpl(none())) => `(cpl(injl(#())))
  | `(cpl(some($e))) => `(cpl(injr($e)))
  | `(cpl(let:m $x := $e1 in $e2)) =>
    `(cpl(match $e1 with | none() => none() | some($x) => $e2))
  | `(cpl(assert($e1) ;;; $e2)) => `(cpl(if $e1 then some($e2) else none()))
  | `(cpl(while $e1 do $e2 end)) =>
    `(cpl((rec &(ConProbLang.binder.BNamed "loop") _ :=
            if $e1 then ($e2; &(ConProbLang.con_prob_lang.expr.Var "loop") #()) else #()) #()))
  | `(cpl(allocn($e1, $e2))) => `(ConProbLang.con_prob_lang.expr.AllocN cpl($e1) cpl($e2))
  | `(cpl(ref($e1))) => `(cpl(allocn(#1, $e1)))
  | `(cpl(! $e1)) => `(ConProbLang.con_prob_lang.expr.Load cpl($e1))
  | `(cpl($e1 ← $e2)) => `(ConProbLang.con_prob_lang.expr.Store cpl($e1) cpl($e2))
  | `(cpl($e1 <- $e2)) => `(cpl($e1 ← $e2))
  | `(cpl(cmpXchg($e1, $e2, $e3))) =>
    `(ConProbLang.con_prob_lang.expr.CmpXchg cpl($e1) cpl($e2) cpl($e3))
  | `(cpl(cas($e1, $e2, $e3))) => `(cpl(snd(cmpXchg($e1, $e2, $e3))))
  | `(cpl(xchg($e1, $e2))) => `(ConProbLang.con_prob_lang.expr.Xchg cpl($e1) cpl($e2))
  | `(cpl(faa($e1, $e2))) => `(ConProbLang.con_prob_lang.expr.FAA cpl($e1) cpl($e2))
  | `(cpl(fork($e1))) => `(ConProbLang.con_prob_lang.expr.Fork cpl($e1))
  | `(cpl(alloc($e1))) => `(ConProbLang.con_prob_lang.expr.AllocTape cpl($e1))
  | `(cpl(rand($e1))) => `(ConProbLang.con_prob_lang.expr.Rand cpl($e1) cpl(#()))
  | `(cpl(rand($α) $e1)) => `(ConProbLang.con_prob_lang.expr.Rand cpl($e1) cpl($α))
  | `(cpl(tick($e1))) => `(ConProbLang.con_prob_lang.expr.Tick cpl($e1))

/-! ## Delaboration -/

/-- delaborating binders -/
@[app_unexpander ConProbLang.binder.BAnon]
def unexpAnon : Unexpander
  | `($_) => `(cpl_binder(_))

@[app_unexpander ConProbLang.binder.BNamed]
def unexpNamed : Unexpander
  | `($_ $s:str) => `(cpl_binder($(Lean.mkIdent <| Name.mkSimple s.getString):ident))
  | _ => throw ()

/-- delaborating literal values (`LitV`), inspecting the literal. -/
@[app_delab ConProbLang.con_prob_lang.val.LitV]
def delabLitV : Delab := do
  if ← getPPOption getPPExplicit then failure
  let e ← SubExpr.getExpr
  let_expr ConProbLang.con_prob_lang.val.LitV l := e | failure
  match l.getAppFnArgs with
  | (``ConProbLang.con_prob_lang.base_lit.LitUnit, #[]) => `(cpl_val(# ()))
  | (``ConProbLang.con_prob_lang.base_lit.LitInt, #[_]) =>
    withNaryArg 0 <| withNaryArg 0 do `(cpl_val(# $(← delab)))
  | (``ConProbLang.con_prob_lang.base_lit.LitBool, #[_]) =>
    withNaryArg 0 <| withNaryArg 0 do `(cpl_val(# $(← delab)))
  | (``ConProbLang.con_prob_lang.base_lit.LitLoc, #[_]) =>
    withNaryArg 0 <| withNaryArg 0 do `(cpl_val(# $(← delab)))
  | (``ConProbLang.con_prob_lang.base_lit.LitLbl, #[_]) =>
    withNaryArg 0 <| withNaryArg 0 do `(cpl_val(#lbl($(← delab))))
  | _ => withNaryArg 0 do `(cpl_val(# $(← delab)))

partial def unexpLamVal : Term → UnexpandM Term
  | `(cpl_val(rec _ $x := $e)) => do
    unexpLamVal <| ← `(cpl_val(λ $x, $e))
  | `(cpl_val(λ $x, (λ $ys*, $e))) => do
    unexpLamVal <| ← `(cpl_val(λ $x $ys*, $e))
  | x => return x

@[app_unexpander ConProbLang.con_prob_lang.val.RecV]
def unexpRecVal : Unexpander
  | `($_ $f $x $e) => do
    unexpLamVal <| ← `(cpl_val(rec $(← unpackCPLBinder f) $(← unpackCPLBinder x) := $(← unpackCPLExp e)))
  | _ => throw ()

partial def unexpPairVal' : Term → UnexpandM Term
  | `(cpl_val((($e1, $e2,*), $e3))) => do
    unexpPairVal' <| ← `(cpl_val(($e1, $e2,*, $e3)))
  | x => return x

@[app_unexpander ConProbLang.con_prob_lang.val.PairV]
def unexpPairVal : Unexpander
  | `($_ $e1 $e2) => do
    unexpPairVal' <| ← `(cpl_val(($(← unpackCPLVal e1), $(← unpackCPLVal e2))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.val.InjLV]
def unexpInjlVal : Unexpander
  | `($_ $e1) => do `(cpl_val(injl($(← unpackCPLVal e1))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.val.InjRV]
def unexpInjrVal : Unexpander
  | `($_ $e1) => do `(cpl_val(injr($(← unpackCPLVal e1))))
  | _ => throw ()

/-- delaborating expressions -/
partial def unexpValLit : Term → UnexpandM Term
  | `(cpl(v(# $l))) => do
    unexpValLit <| ← `(cpl(# $l))
  | `(cpl(v(#lbl($l)))) => do
    unexpValLit <| ← `(cpl(#lbl($l)))
  | x => return x

@[app_unexpander ConProbLang.con_prob_lang.expr.Val]
def unexpVal : Unexpander
  | `($_ $v) => do unexpValLit <| ← `(cpl(v($(← unpackCPLVal v))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.Var]
def unexpVar : Unexpander
  | `($_ $e:str) => do `(cpl($(Lean.mkIdent <| Name.mkSimple e.getString):ident))
  | _ => throw ()

/-- delaborating binary operations, inspecting the operator. -/
@[app_delab ConProbLang.con_prob_lang.expr.BinOp]
def delabBinOp : Delab := do
  if ← getPPOption getPPExplicit then failure
  let e ← SubExpr.getExpr
  let_expr ConProbLang.con_prob_lang.expr.BinOp op _ _ := e | failure
  let some opName := op.constName? | failure
  let e1 ← unpackCPLExp (← withNaryArg 1 delab)
  let e2 ← unpackCPLExp (← withNaryArg 2 delab)
  match opName with
  | ``ConProbLang.con_prob_lang.bin_op.PlusOp => `(cpl(($e1 + $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.OffsetOp => `(cpl(($e1 +ₗ $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.MinusOp => `(cpl(($e1 - $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.MultOp => `(cpl(($e1 * $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.QuotOp => `(cpl(($e1 / $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.RemOp => `(cpl(($e1 % $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.AndOp => `(cpl(($e1 &&& $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.OrOp => `(cpl(($e1 ||| $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.XorOp => `(cpl(($e1 ^^^ $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.ShiftLOp => `(cpl(($e1 <<< $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.ShiftROp => `(cpl(($e1 >>> $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.LeOp => `(cpl(($e1 ≤ $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.LtOp => `(cpl(($e1 < $e2)))
  | ``ConProbLang.con_prob_lang.bin_op.EqOp => `(cpl(($e1 = $e2)))
  | _ => failure

/-- delaborating unary operations, inspecting the operator. -/
@[app_delab ConProbLang.con_prob_lang.expr.UnOp]
def delabUnOp : Delab := do
  if ← getPPOption getPPExplicit then failure
  let e ← SubExpr.getExpr
  let_expr ConProbLang.con_prob_lang.expr.UnOp op _ := e | failure
  let some opName := op.constName? | failure
  let e1 ← unpackCPLExp (← withNaryArg 1 delab)
  match opName with
  | ``ConProbLang.con_prob_lang.un_op.NegOp => `(cpl((~$e1)))
  | ``ConProbLang.con_prob_lang.un_op.MinusUnOp => `(cpl((-$e1)))
  | _ => failure

@[app_unexpander ConProbLang.con_prob_lang.expr.If]
def unexpIf : Unexpander
  | `($_ $e1 $e2 $e3) => do
    `(cpl(if $(← unpackCPLExp e1) then $(← unpackCPLExp e2) else $(← unpackCPLExp e3)))
  | _ => throw ()

partial def unexpLam : Term → UnexpandM Term
  | `(cpl((rec _ $x := $e))) => do
    unexpLam <| ← `(cpl((λ $x, $e)))
  | `(cpl((λ $x, (λ $ys*, $e)))) => do
    unexpLam <| ← `(cpl((λ $x $ys*, $e)))
  | x => return x

@[app_unexpander ConProbLang.con_prob_lang.expr.Rec]
def unexpRec : Unexpander
  | `($_ $f $x $e) => do
    unexpLam <| ← `(cpl((rec $(← unpackCPLBinder f) $(← unpackCPLBinder x) := $(← unpackCPLExp e))))
  | _ => throw ()

partial def unexpLet : Term → UnexpandM Term
  | `(cpl((λ $f, $e2) $e1)) => do
    unexpLet <| ← `(cpl(let $f := $e1; $e2))
  | `(cpl(let _ := $e1; $e2)) => do `(cpl($e1; $e2))
  | x => return x

@[app_unexpander ConProbLang.con_prob_lang.expr.App]
def unexpApp : Unexpander
  | `($_ $e1 $e2) => do
    unexpLet <| ← `(cpl($(← unpackCPLExp e1) $(← unpackCPLExp e2)))
  | _ => throw ()

partial def unexpPair' : Term → UnexpandM Term
  | `(cpl((($e1, $e2,*), $e3))) => do
    unexpPair' <| ← `(cpl(($e1, $e2,*, $e3)))
  | x => return x

@[app_unexpander ConProbLang.con_prob_lang.expr.Pair]
def unexpPair : Unexpander
  | `($_ $e1 $e2) => do
    unexpPair' <| ← `(cpl(($(← unpackCPLExp e1), $(← unpackCPLExp e2))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.Fst]
def unexpFst : Unexpander
  | `($_ $e1) => do `(cpl(fst($(← unpackCPLExp e1))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.Snd]
def unexpSnd : Unexpander
  | `($_ $e1) => do `(cpl(snd($(← unpackCPLExp e1))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.InjL]
def unexpInjl : Unexpander
  | `($_ $e1) => do `(cpl(injl($(← unpackCPLExp e1))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.InjR]
def unexpInjr : Unexpander
  | `($_ $e1) => do `(cpl(injr($(← unpackCPLExp e1))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.Case]
def unexpCase : Unexpander
  | `($_ $e1 cpl((λ $i2, $e2)) cpl((λ $i3, $e3))) =>
    do `(cpl(match $(← unpackCPLExp e1) with | injl($i2) => $e2 | injr($i3) => $e3))
  | _ => throw ()

partial def unexpRef : Term → UnexpandM Term
  | `(cpl(allocn(#1, $e2))) => do `(cpl(ref($e2)))
  | x => return x

@[app_unexpander ConProbLang.con_prob_lang.expr.AllocN]
def unexpAllocN : Unexpander
  | `($_ $e1 $e2) => do unexpRef <| ← `(cpl(allocn($(← unpackCPLExp e1), $(← unpackCPLExp e2))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.Load]
def unexpLoad : Unexpander
  | `($_ $e1) => do `(cpl(!$(← unpackCPLExp e1)))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.Store]
def unexpStore : Unexpander
  | `($_ $e1 $e2) => do `(cpl($(← unpackCPLExp e1) ← $(← unpackCPLExp e2)))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.CmpXchg]
def unexpCmpXChg : Unexpander
  | `($_ $e1 $e2 $e3) => do
    `(cpl(cmpXchg($(← unpackCPLExp e1), $(← unpackCPLExp e2), $(← unpackCPLExp e3))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.Xchg]
def unexpXChg : Unexpander
  | `($_ $e1 $e2) => do `(cpl(xchg($(← unpackCPLExp e1), $(← unpackCPLExp e2))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.FAA]
def unexpFAA : Unexpander
  | `($_ $e1 $e2) => do `(cpl(faa($(← unpackCPLExp e1), $(← unpackCPLExp e2))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.Fork]
def unexpFork : Unexpander
  | `($_ $e1) => do `(cpl(fork($(← unpackCPLExp e1))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.AllocTape]
def unexpAllocTape : Unexpander
  | `($_ $e1) => do `(cpl(alloc($(← unpackCPLExp e1))))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.Rand]
def unexpRand : Unexpander
  | `($_ $e1 cpl(#())) => do `(cpl(rand($(← unpackCPLExp e1))))
  | `($_ $e1 $e2) => do `(cpl(rand($(← unpackCPLExp e2)) $(← unpackCPLExp e1)))
  | _ => throw ()

@[app_unexpander ConProbLang.con_prob_lang.expr.Tick]
def unexpTick : Unexpander
  | `($_ $e1) => do `(cpl(tick($(← unpackCPLExp e1))))
  | _ => throw ()

end con_prob_lang
end ConProbLang

end
