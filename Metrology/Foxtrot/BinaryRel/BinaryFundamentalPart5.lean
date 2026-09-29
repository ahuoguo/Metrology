module

public import Metrology.Foxtrot.BinaryRel.BinaryFundamentalPart4

/-!
# The fundamental theorem of Foxtrot's binary logical relation (part 5)

Ported from clutch/theories/foxtrot/binary_rel/binary_fundamental.v (lines 717-864: section
`bin_log_related_under_typed_ctx`).

## Rocq → Lean map
* `bin_log_related_under_typed_ctx`: same name (namespace `Foxtrot.BinaryRel`).

## Deviations
* The proof is by induction on the derivation of `typed_ctx K Γ τ Γ' τ'` followed by a case
  analysis on the typed context item (Rocq: induction on `K`, then `inversion_clear`).
* The Rocq statement ends in `(∀ Δ, ..)%I` after a wand; here it is an entailment.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

section bin_log_related_under_typed_ctx

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `bin_log_related_under_typed_ctx` (precongruence). -/
theorem bin_log_related_under_typed_ctx (Γ : varmap type) (e e' : expr) (τ : type)
    (Γ' : varmap type) (τ' : type) (K : ctx) (hK : typed_ctx K Γ τ Γ' τ') :
    (□ ∀ Δ : List (lrel GF), 〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ) ⊢
      ∀ Δ : List (lrel GF), 〈Δ;Γ'〉 ⊨ fill_ctx K e ≤log≤ fill_ctx K e' : τ' := by
  induction hK with
  | TPCTX_nil Γ τ =>
    simp only [fill_ctx_nil]
    iintro #H %Δ
    iapply H
  | TPCTX_cons Γ1 τ1 Γ2 τ2 Γ3 τ3 k K hk _ ih =>
    have ihΔ : ∀ Δ : List (lrel GF), (□ ∀ Δ : List (lrel GF), 〈Δ;Γ1〉 ⊨ e ≤log≤ e' : τ1) ⊢
        〈Δ;Γ2〉 ⊨ fill_ctx K e ≤log≤ fill_ctx K e' : τ2 :=
      fun Δ => ih.trans (forall_elim Δ)
    simp only [fill_ctx_cons]
    iintro #Hrel %Δ
    cases hk with
    | TP_CTX_Rec _ τ τ' f x =>
      simp only [fill_ctx_item]
      iapply bin_log_related_rec
      imodintro
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_AppL _ e2 τ τ' h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_app $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h
    | TP_CTX_AppR _ e1 τ τ' h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_app _ _ _ _ _ _ τ2 $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_UnOp_Nat op _ τ hop =>
      simp only [fill_ctx_item]
      iapply bin_log_related_int_unop _ _ _ _ _ _ hop
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_UnOp_Bool op _ τ hop =>
      simp only [fill_ctx_item]
      iapply bin_log_related_bool_unop _ _ _ _ _ _ hop
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_BinOpL_Nat op _ e2 τ h hop =>
      simp only [fill_ctx_item]
      iapply bin_log_related_int_binop _ _ _ _ _ _ _ _ hop $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h
    | TP_CTX_BinOpR_Nat op e1 _ τ h hop =>
      simp only [fill_ctx_item]
      iapply bin_log_related_int_binop _ _ _ _ _ _ _ _ hop $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_BinOpL_Bool op _ e2 τ h hop =>
      simp only [fill_ctx_item]
      iapply bin_log_related_bool_binop _ _ _ _ _ _ _ _ hop $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h
    | TP_CTX_BinOpR_Bool op e1 _ τ h hop =>
      simp only [fill_ctx_item]
      iapply bin_log_related_bool_binop _ _ _ _ _ _ _ _ hop $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_BinOpL_UnboxedEq e2 _ τ hu h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_unboxed_eq _ _ _ _ _ _ _ hu $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h
    | TP_CTX_BinOpR_UnboxedEq e1 _ τ hu h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_unboxed_eq _ _ _ _ _ _ _ hu $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_IfL _ e1 e2 τ h1 h2 =>
      simp only [fill_ctx_item]
      iapply bin_log_related_if $$ [] [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h1
      · iapply fundamental Δ _ _ _ h2
    | TP_CTX_IfM _ e0 e2 τ h0 h2 =>
      simp only [fill_ctx_item]
      iapply bin_log_related_if $$ [] [] []
      · iapply fundamental Δ _ _ _ h0
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h2
    | TP_CTX_IfR _ e0 e1 τ h0 h1 =>
      simp only [fill_ctx_item]
      iapply bin_log_related_if $$ [] [] []
      · iapply fundamental Δ _ _ _ h0
      · iapply fundamental Δ _ _ _ h1
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_PairL _ e2 τ τ' h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_pair $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h
    | TP_CTX_PairR _ e1 τ τ' h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_pair $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_Fst _ τ τ' =>
      simp only [fill_ctx_item]
      iapply bin_log_related_fst _ _ _ _ _ τ'
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_Snd _ τ τ' =>
      simp only [fill_ctx_item]
      iapply bin_log_related_snd _ _ _ _ τ
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_InjL _ τ τ' =>
      simp only [fill_ctx_item]
      iapply bin_log_related_injl
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_InjR _ τ τ' =>
      simp only [fill_ctx_item]
      iapply bin_log_related_injr
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_CaseL _ e1 e2 τ1 τ2 τ' h1 h2 =>
      simp only [fill_ctx_item]
      iapply bin_log_related_case $$ [] [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h1
      · iapply fundamental Δ _ _ _ h2
    | TP_CTX_CaseM _ e0 e2 τ1 τ2 τ' h0 h2 =>
      simp only [fill_ctx_item]
      iapply bin_log_related_case _ _ _ _ _ _ _ _ τ1 τ2 $$ [] [] []
      · iapply fundamental Δ _ _ _ h0
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h2
    | TP_CTX_CaseR _ e0 e1 τ1 τ2 τ' h0 h1 =>
      simp only [fill_ctx_item]
      iapply bin_log_related_case _ _ _ _ _ _ _ _ τ1 τ2 $$ [] [] []
      · iapply fundamental Δ _ _ _ h0
      · iapply fundamental Δ _ _ _ h1
      · iapply ihΔ Δ $$ Hrel
    | TPCTX_Alloc _ τ =>
      simp only [fill_ctx_item]
      iapply bin_log_related_alloc
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_Load _ τ =>
      simp only [fill_ctx_item]
      iapply bin_log_related_load
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_StoreL _ e2 τ h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_store $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h
    | TP_CTX_StoreR _ e1 τ h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_store _ _ _ _ _ _ τ2 $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_Fold _ τ =>
      simp only [fill_ctx_item]
      iapply bin_log_related_fold
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_Unfold _ τ =>
      simp only [fill_ctx_item]
      iapply bin_log_related_unfold
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_TLam _ τ =>
      simp only [fill_ctx_item]
      iapply bin_log_related_tlam
      iintro %A
      imodintro
      iapply ihΔ (A :: Δ) $$ Hrel
    | TP_CTX_TApp _ τ τ' =>
      simp only [fill_ctx_item]
      iapply bin_log_related_tapp'
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_UnpackL x e2 _ τ τ2 h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_unpack $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iintro %A
        iapply fundamental (A :: Δ) _ _ _ h
    | TP_CTX_UnpackR x e1 _ τ τ2 h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_unpack _ _ _ _ _ _ _ τ $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iintro %A
        iapply ihΔ (A :: Δ) $$ Hrel
    | TP_CTX_AllocTape _ =>
      simp only [fill_ctx_item]
      iapply bin_log_related_alloctape
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_RandUnitL _ e2 h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_rand_unit $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h
    | TP_CTX_RandTapeL _ e2 h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_rand_tape $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h
    | TP_CTX_RandUnitR _ e1 h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_rand_unit $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_RandTapeR _ e1 h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_rand_tape $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_Fork _ =>
      simp only [fill_ctx_item]
      iapply bin_log_related_fork
      iapply ihΔ Δ $$ Hrel
    | TP_CTX_CmpXchgL _ e1 e2 τ hu h1 h2 =>
      simp only [fill_ctx_item]
      iapply bin_log_related_CmpXchg _ _ _ _ _ _ _ _ _ hu $$ [] [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h1
      · iapply fundamental Δ _ _ _ h2
    | TP_CTX_CmpXchgM _ e0 e2 τ hu h0 h2 =>
      simp only [fill_ctx_item]
      iapply bin_log_related_CmpXchg _ _ _ _ _ _ _ _ _ hu $$ [] [] []
      · iapply fundamental Δ _ _ _ h0
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h2
    | TP_CTX_CmpXchgR _ e0 e1 τ hu h0 h1 =>
      simp only [fill_ctx_item]
      iapply bin_log_related_CmpXchg _ _ _ _ _ _ _ _ _ hu $$ [] [] []
      · iapply fundamental Δ _ _ _ h0
      · iapply fundamental Δ _ _ _ h1
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_XchgL _ e2 τ h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_xchg $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h
    | TP_CTX_XchgR _ e1 τ h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_xchg _ _ _ _ _ _ τ2 $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iapply ihΔ Δ $$ Hrel
    | TP_CTX_FAAL _ e2 h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_FAA $$ [] []
      · iapply ihΔ Δ $$ Hrel
      · iapply fundamental Δ _ _ _ h
    | TP_CTX_FAAR _ e1 h =>
      simp only [fill_ctx_item]
      iapply bin_log_related_FAA $$ [] []
      · iapply fundamental Δ _ _ _ h
      · iapply ihΔ Δ $$ Hrel

end bin_log_related_under_typed_ctx

end Foxtrot.BinaryRel
