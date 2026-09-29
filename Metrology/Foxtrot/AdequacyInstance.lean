module

public import Metrology.Foxtrot.Adequacy

/-!
# A concrete functor list for Foxtrot adequacy

Rocq: `foxtrotΣ` and `subG_foxtrotGPreS` (clutch/theories/foxtrot/primitive_laws.v). The name
`foxtrotΣ` is `foxtrotSigma`, since `Σ` is not an identifier character in Lean.

iris-lean has no `gFunctors` lists or `subG`: a `BundledGFunctors` is a function
`GType → GFunctor`, and `ElemG` instances are given by an index and `rfl`. This file follows the
template of iris-lean's `HeapLangS` / `instHeapLangGS_HeapLangS`:

* `foxtrotSigma : BundledGFunctors` lists the functors needed by `foxtrotGpreS` (invariants,
  later credits, the LHS heap and tapes, the spec thread pool, error credits). As in Rocq, the
  LHS and spec heaps (resp. tapes) use the same functor, so the corresponding `GhostMapG`
  instances coincide (they are distinguished by their ghost names).
* `foxtrotGpreS_foxtrotSigma : foxtrotGpreS foxtrotSigma` (Rocq: `subG_foxtrotGPreS`, specialised to
  `foxtrotSigma`).
* `foxtrot_adequacy_closed`: `foxtrot_adequacy` instantiated at `foxtrotSigma`, so that its
  `foxtrotGpreS` hypothesis is discharged (a sanity check that the adequacy theorem is usable).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

/-- Rocq: `foxtrotΣ`. -/
def foxtrotSigma : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Loc (Agree (DiscreteO val)) locF), by infer_instance⟩
  | 5 => ⟨constOF (HeapView Loc (Agree (DiscreteO tape)) locF), by infer_instance⟩
  | 6 => ⟨constOF (HeapView ℕ (Agree (DiscreteO expr)) tpoolF), by infer_instance⟩
  | 7 => ⟨constOF (Auth ErrorCredit), by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

/-- Rocq: `subG_foxtrotGPreS` (at `foxtrotSigma`). -/
instance foxtrotGpreS_foxtrotSigma : foxtrotGpreS foxtrotSigma where
  foxtrotGpreS_iris := {
    toWsatGpreS := ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩⟩
    toLcGpreS := ⟨⟨3, rfl⟩⟩ }
  foxtrotGpreS_heap := ⟨⟨4, rfl⟩⟩
  foxtrotGpreS_tapes := ⟨⟨5, rfl⟩⟩
  foxtrotGpreS_spec := ⟨⟨⟨6, rfl⟩⟩, ⟨⟨4, rfl⟩⟩, ⟨⟨5, rfl⟩⟩⟩
  foxtrotGpreS_err := ⟨⟨7, rfl⟩⟩

/-- `foxtrot_adequacy` at the concrete functor list `foxtrotSigma` (not in Rocq). -/
theorem foxtrot_adequacy_closed (ϕ : val → val → Prop) (e e' : expr) (σ σ' : state)
    (ε : ℝ≥0∞)
    (Hwp : ∀ [foxtrotGS foxtrotSigma], ⊢@{IProp foxtrotSigma} ↯ ε -∗ 0 ⤇ e' -∗
      WP e {{ v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }}) :
    lub_termination_prob e σ ≤ lub_termination_prob e' σ' + ε :=
  foxtrot_adequacy foxtrotSigma ϕ e e' σ σ' ε Hwp

end Foxtrot
