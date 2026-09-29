module

public import Metrology.Coneris.PrimitiveLaws
public import Iris.BI.Lib.Atomic
public import Iris.Instances.Lib.Invariants

/-!
# Logically atomic triples for Coneris

Ported from clutch/theories/coneris/atomic.v

Not described in the Coneris paper: an atomic WP `atomic_wp e E α β POST f`, stated in terms of
iris-lean's atomic updates (`Iris.BI.Lib.Atomic`, the port of `iris.bi.lib.atomic`) and the
Coneris WP (`pgl_wp'`). The inner mask is hard-coded to be empty, and the non-atomic
postcondition is an `Option (IProp GF)` combined with `-∗?`.

## Design choices (Rocq → Lean)

* The file follows iris-lean's `ProgramLogic/Atomic.lean` (which ports the same Rocq file for
  iris's own WP): telescopes are iris-lean's `Tele`, `tele_app`/`λ..` are `Tele.lam`/`λ..`,
  and `rewrite ->!tele_app_bind` is `isimp only [Tele.app_bind]`.
* Notation: the `<<{ ∀∀ x, α }>> e @ E <<{ ∃∃ y, β | z, RET v ; POST }>>` syntax is iris-lean's
  (`Iris.atomicWpNotation`, which covers all 16 Rocq variants); inside `namespace Coneris` (or
  with `open Coneris`) a scoped `macro_rules` makes it elaborate to `Coneris.atomic_wp`.
* All lemmas are entailments `A ⊢ B` (Rocq `A -∗ B`, as in iris-lean); `atomic_wp_inv` is
  `A ⊢ inv N I -∗ B`. The `TCEq (to_val e) None`
  premise is a plain hypothesis `h : to_val e = none`.
* `atomic_seq_wp_atomic` requires ConProbLang's `Atomic StronglyAtomic e` (as in Rocq; needed by
  `pgl_wp_atomic`).

## Added
* `into_wand_atomic_wp` (Rocq's `iApply` unfolds the definition `atomic_wp`; iris-lean's
  instance search does not), so that `awp_apply lem` works for `lem : ⊢ atomic_wp ..`.

## Omitted
Nothing (the 8 Rocq `Notation`s are subsumed by iris-lean's single syntax).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris

section definition

variable {GF : BundledGFunctors} [conerisGS GF] {TA TB TP : Tele}

/-- Rocq: `atomic_wp`. The (outer) user mask is what is left after the implementation opened
its things. -/
def atomic_wp (e : expr) (E : CoPset) (α : TA.Arg → IProp GF)
    (β : TA.Arg → TB.Arg → IProp GF) (POST : TA.Arg → TB.Arg → TP.Arg → Option (IProp GF))
    (f : TA.Arg → TB.Arg → TP.Arg → val) : IProp GF :=
  iprop(∀ Φ, atomic_update (⊤ \ E) ∅ α β
    (λ.. x y, iprop(∀.. z, POST x y z -∗? Φ (f x y z))) -∗ WP e {{ Φ }})

/-- Helper (not in Rocq, where `iApply` unfolds `atomic_wp`): `iapply`/`wp_apply`/`awp_apply`
of a lemma `⊢ atomic_wp e E α β POST f` see through the definition. -/
instance into_wand_atomic_wp {p q : Bool} {m : WandMode} {e : expr} {E : CoPset}
    {α : TA.Arg → IProp GF} {β : TA.Arg → TB.Arg → IProp GF}
    {POST : TA.Arg → TB.Arg → TP.Arg → Option (IProp GF)} {f : TA.Arg → TB.Arg → TP.Arg → val}
    {P Q : IProp GF}
    [h : IntoWand p q iprop(∀ Φ, atomic_update (⊤ \ E) ∅ α β
      (λ.. x y, iprop(∀.. z, POST x y z -∗? Φ (f x y z))) -∗ WP e {{ Φ }}) m P Q] :
    IntoWand p q (atomic_wp e E α β POST f) m P Q := h

end definition

/-! ## Notation -/

public meta section
open Lean

scoped macro_rules
  | `(iprop(<<{%$tk $[$xs]? $α }>> $e @ $E <<{ $[$ys]? $β | $[$zs]? RET $v $[; $POST]? }>>)) => do
    let (TA, TB, TP, α, β, POST, f) ← Iris.awpArgs xs ys zs α β v POST
    ``($(wrapIprop tk ``Coneris.atomic_wp) (TA := $TA) (TB := $TB) (TP := $TP) $e $E $α $β $POST $f)

end

/-! ## Theory -/

section lemmas

variable {GF : BundledGFunctors} [conerisGS GF]
variable {TA TB TP : Tele} {e : expr} {E : CoPset}
variable {α : TA.Arg → IProp GF} {β : TA.Arg → TB.Arg → IProp GF}
variable {POST : TA.Arg → TB.Arg → TP.Arg → Option (IProp GF)}
variable {f : TA.Arg → TB.Arg → TP.Arg → val}

/-- Rocq: `atomic_wp_seq`. Atomic triples imply sequential triples. -/
theorem atomic_wp_seq :
    atomic_wp e E α β POST f ⊢
    ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e {{ Φ }} := by
  iunfold atomic_wp
  iintro Hwp %Φ %x Hα HΦ
  iapply pgl_wp_frame_wand $$ HΦ
  iapply Hwp
  iauintro
  iaaccintro Hα
  · iintro $
  · iintro %y Hβ !>
    isimp only [Tele.app_bind]
    iintro %z Hpost HΦ
    iapply HΦ $$ Hβ Hpost

/-- Rocq: `atomic_wp_seq_step`. This version matches the Texan triple, i.e., with a later in
front of the `(∀.. y, β x y -∗ Φ (f x y))`. -/
theorem atomic_wp_seq_step (h : to_val e = none) :
    atomic_wp e E α β POST f ⊢
    ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e {{ Φ }} := by
  iintro Hwp %Φ %x Hα HΦ
  iapply pgl_wp_step_fupd h LawfulSet.subset_refl $$ [$HΦ //]
  iapply atomic_wp_seq $$ Hwp Hα
  iintro %y Hβ %z Hpost HΦ
  iapply HΦ $$ Hβ Hpost

/-- Rocq: `atomic_seq_wp_atomic`. Sequential triples with the empty mask for a physically
atomic `e` are atomic. -/
theorem atomic_seq_wp_atomic [Atomic (Λ := con_prob_lang) StronglyAtomic e] :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e @ ∅ {{ Φ }}) ⊢
    atomic_wp e E α β POST f := by
  iunfold atomic_wp
  iintro Hwp %Φ AU
  imod AU with ⟨%x, Hα, -, Hclose⟩
  iapply Hwp $$ Hα
  iintro %y Hβ %z Hpost
  imod Hclose $$ Hβ with HΦ
  isimp only [Tele.app_bind] at HΦ
  iapply HΦ $$ Hpost

/-- Rocq: `persistent_seq_wp_atomic`. Sequential triples with a persistent precondition and no
initial quantifier are atomic. -/
theorem persistent_seq_wp_atomic {α : Tele.Arg .nil → IProp GF}
    {β : Tele.Arg .nil → TB.Arg → IProp GF}
    {POST : Tele.Arg .nil → TB.Arg → TP.Arg → Option (IProp GF)}
    {f : Tele.Arg .nil → TB.Arg → TP.Arg → val} [Persistent (α .nil)] :
    (∀ Φ, α .nil -∗
      (∀.. y, β .nil y -∗ ∀.. z, POST .nil y z -∗? Φ (f .nil y z)) -∗ WP e {{ Φ }}) ⊢
    atomic_wp e E α β POST f := by
  iunfold atomic_wp
  iintro Hwp %Φ HΦ
  iapply fupd_pgl_wp
  imod HΦ with ⟨%⟨⟩, #Hα, Hclose, -⟩
  imod Hclose $$ Hα with HΦ
  iapply pgl_wp_fupd
  iapply Hwp $$ Hα
  iintro !> %y Hβ %z Hpost
  imod HΦ with ⟨%⟨⟩, -, -, Hclose⟩
  imod Hclose $$ Hβ with HΦ
  isimp only [Tele.lam, Tele.app, Tele.bind, Tele.app_bind] at HΦ
  iapply HΦ $$ Hpost

/-- Rocq: `atomic_wp_mask_weaken`. -/
theorem atomic_wp_mask_weaken {E₁ E₂ : CoPset} (HE : E₁ ⊆ E₂) :
    atomic_wp e E₁ α β POST f ⊢ atomic_wp e E₂ α β POST f := by
  iunfold atomic_wp
  iintro Hwp %Φ AU
  iapply Hwp
  iapply atomic_update_mask_weaken (LawfulSet.diff_subset_diff_right HE) $$ AU

/-- Rocq: `atomic_wp_inv`. We can open invariants around atomic triples.
(Just for demonstration purposes; we always use `iinv` in proofs.) -/
theorem atomic_wp_inv {N : Namespace} {I : IProp GF} (HN : (↑N : CoPset) ⊆ E) :
    atomic_wp e (E \ ↑N) (λ.. x, iprop(▷ I ∗ α x)) (λ.. x y, iprop(▷ I ∗ β x y)) POST f ⊢
    inv N I -∗ atomic_wp e E α β POST f := by
  iunfold atomic_wp
  iintro Hwp #Hinv %Φ AU
  iapply Hwp
  iauintro
  iinv N with HI
  · exact ⟨fun x hx => LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h =>
      (LawfulSet.mem_diff.mp h).right hx⟩, trivial⟩
  iapply aacc_aupd $$ AU
  · intro x hx
    simp only [LawfulSet.mem_diff] at hx ⊢
    exact ⟨⟨CoPset.mem_full, fun h => hx.right h.left⟩, fun h => hx.right (HN x h)⟩
  iintro %x Hα
  iaaccintro %x [HI Hα] <;> isimp only [Tele.app_bind]
  · iframe
  · iintro ⟨HI, $⟩
    iintro !> AU !>
    simp []
    iframe
  · iintro %y H
    icases H with ⟨HI, Hβ⟩
    imodintro
    iright
    iexists y
    iintro {$Hβ} HΦ !>
    simp []
    iframe HI HΦ

end lemmas

section tests

variable {GF : BundledGFunctors} [conerisGS GF]

/-- The atomic-triple notation elaborates to `Coneris.atomic_wp`. -/
example (e : expr) (P : ℕ → IProp GF) (Q : ℕ → ℕ → IProp GF) :
    iprop(<<{ ∀∀ x, P x }>> e @ ∅ <<{ ∃∃ y, Q x y | RET (LitV (LitInt y)) }>>) ⊢
    iprop(<<{ ∀∀ x, P x }>> e @ ⊤ <<{ ∃∃ y, Q x y | RET (LitV (LitInt y)) }>>) :=
  atomic_wp_mask_weaken LawfulSet.empty_subset

end tests

end Coneris
