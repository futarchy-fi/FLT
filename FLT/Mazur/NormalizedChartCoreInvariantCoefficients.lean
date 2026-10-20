/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreMixedCoefficientDetection
public import FLT.Mazur.EquivalenceRelationNormalizedFrameEtale
public import FLT.Mazur.EquivalenceRelationNormalizedFrameFree
public import FLT.Mazur.FiniteGroupOpenRestriction
public import FLT.Mazur.SchemeFiniteGroupQuotient

/-!
# Actual invariant chart coefficients from original core values

Full sections on the old normalized chart with prescribed invariant values
on every covering core order belong to that chart's actual invariant ring.
The proof uses the original endpoint-moving action arrows and all-order
mixed detection. It does not replace that ring by the full section ring.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance endoCoreOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance endoCoreOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance endoCoreOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCore rankStageCoreOriginalMap

/-- Original core values force any endpoint-moving source endomorphism to fix a section. -/
theorem endomorphism_eq_of_core_values [IsLocallyNoetherian B]
    (g : B ⟶ A) (u : B ⟶ B) (δ : B ⟶ D) (hδ : δ ≫ p = g) (hδ' : δ ≫ q = u ≫ g)
    {ι : Type} (n : ι → ℕ) (a b : ι → Γ(A, ⊤))
    (ha : ∀ i, A.basicOpen (a i) ≤ rankImageOpen (Over.mk p) (n i))
    (h : ∀ i k, rankThickeningMap (Over.mk p) (n i) k ⁻¹ᵁ A.basicOpen (b i) ≤
      rankStageCore e (n i) (a i) (ha i) k)
    (hcover : ∀ x : B, ∃ i, g x ∈ exactRank (Over.mk p) (n i) ∧ g x ∈ A.basicOpen (b i))
    (s : Γ(B, ⊤)) (w : ∀ i k, rankStageCoreInvariants e (n i) (a i) (ha i) k)
    (hs : ∀ i k,
      (pullback.snd (rankStageCoreOriginalMap e (n i) (a i) (ha i) k) g).appTop s =
        (pullback.fst (rankStageCoreOriginalMap e (n i) (a i) (ha i) k) g).appTop (w i k).val) :
    u.appTop s = s := by
  have hf : δ ≫ p = (𝟙 B) ≫ g := by rw [Category.id_comp, hδ]
  have hc : ∀ x : B, ∃ i,
      (δ ≫ p) x ∈ exactRank (Over.mk p) (n i) ∧ (δ ≫ p) x ∈ A.basicOpen (b i) := by
    rw [hδ]
    exact hcover
  have he := mixed_equation_of_core_values e g g (𝟙 B) u δ hf hδ'
    n a b ha h hc s s w hs hs
  exact he.symm

end FLT.Mazur.EquivalenceRelationOrderedFrames

namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option quotPrecheck false
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance chartCoreOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance chartCoreOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance chartCoreOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (I : Type) [Fintype I] (o : I) (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
/-- A sealed original source map keeps coefficient comparisons on the unchanged chart. -/
@[irreducible]
def chartCoreCoefficientMap : U.toScheme ⟶ A := U.ι ≫ first p q I o

omit [Etale p] [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  [IsAffine A] [LocallyQuasiFinite p] in
/-- The sealed map is exactly the original chart endpoint. -/
theorem chartCoreCoefficientMap_eq :
    chartCoreCoefficientMap (p := p) (q := q) I o U = U.ι ≫ first p q I o := by
  unfold chartCoreCoefficientMap
  rfl

local notation "g" => (chartCoreCoefficientMap (p := p) (q := q) I o U : U.toScheme ⟶ A)
local notation "ρ" => restrictedAction (action e I o) U hU
attribute [local irreducible] rankStageCore rankStageCoreOriginalMap source action
  first actionArrow restrictedAction
omit [QuasiCompact p] [Etale q] [IsAffine A] [LocallyQuasiFinite p] in
include e in
/-- The original chart inherits local Noetherianity through its etale source map. -/
theorem chartCore_locallyNoetherian : IsLocallyNoetherian U.toScheme := by
  let _ := first_etale e I o
  let _ := LocallyOfFiniteType.isLocallyNoetherian (first p q I o)
  exact isLocallyNoetherian_of_isOpenImmersion U.ι

omit [Etale p] [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  [IsAffine A] [LocallyQuasiFinite p] in
/-- The original action arrow starts at the sealed chart source map. -/
theorem chartCore_action_first (σ : Equiv.Perm I) :
    (U.ι ≫ actionArrow (p := p) (q := q) I o σ) ≫ p = g := by
  rw [chartCoreCoefficientMap_eq, Category.assoc, actionArrow_first]

omit [Etale p] [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  [IsAffine A] [LocallyQuasiFinite p] in
/-- Its second endpoint is the original endpoint-moving restricted action. -/
theorem chartCore_action_second (σ : Equiv.Perm I) :
    (U.ι ≫ actionArrow (p := p) (q := q) I o σ) ≫ q = (ρ σ).hom ≫ g := by
  rw [chartCoreCoefficientMap_eq, Category.assoc, actionArrow_second, ← Category.assoc,
    ← restrictedAction_hom_ι, Category.assoc]

variable {ι : Type} (n : ι → ℕ) (a b : ι → Γ(A, ⊤))
  (ha : ∀ i, A.basicOpen (a i) ≤ rankImageOpen (Over.mk p) (n i))
  (h : ∀ i k, rankThickeningMap (Over.mk p) (n i) k ⁻¹ᵁ A.basicOpen (b i) ≤
    rankStageCore e (n i) (a i) (ha i) k)
  (hcover : ∀ x : U.toScheme, ∃ i,
    chartCoreCoefficientMap (p := p) (q := q) I o U x ∈ exactRank (Over.mk p) (n i) ∧
    chartCoreCoefficientMap (p := p) (q := q) I o U x ∈ A.basicOpen (b i))
  (s : Γ(U.toScheme, ⊤)) (w : ∀ i k, rankStageCoreInvariants e (n i) (a i) (ha i) k)
  (hs : ∀ i k,
    (pullback.snd (rankStageCoreOriginalMap e (n i) (a i) (ha i) k)
      (chartCoreCoefficientMap (p := p) (q := q) I o U)).appTop s =
      (pullback.fst (rankStageCoreOriginalMap e (n i) (a i) (ha i) k)
        (chartCoreCoefficientMap (p := p) (q := q) I o U)).appTop (w i k).val)

include h hcover hs in
/-- Every actual old chart action fixes the original section candidate. -/
theorem chartSection_core_values_invariant (σ : Equiv.Perm I) : (ρ σ).hom.appTop s = s := by
  have hN := chartCore_locallyNoetherian e I o U
  have h₁ := @chartCore_action_first D A p q ‹IsSeparated p› I inferInstance o U σ
  have h₂ := @chartCore_action_second D A p q ‹IsSeparated p› e I inferInstance o U hU σ
  refine @endomorphism_eq_of_core_values D A U.toScheme p q
    ‹IsSeparated p› ‹Etale p› ‹QuasiCompact p› ‹Etale q› ‹IsLocallyNoetherian A›
    ‹IsAffine A› ‹LocallyQuasiFinite p› e hN g (ρ σ).hom
    (U.ι ≫ actionArrow (p := p) (q := q) I o σ) h₁ h₂ ι n a b ha h hcover s
      (fun i k ↦ w i k) ?_
  intro i k
  exact hs i k

/-- The candidate is promoted to the actual invariant ring, with its original section unchanged. -/
def chartInvariantOfCoreValues : invariantCoordinates ρ := by
  refine ⟨s, fun σ ↦ ?_⟩
  exact chartSection_core_values_invariant e I o U hU n a b ha h hcover s w hs σ⁻¹

/-- No correction or change of coefficient ring is hidden in the promotion. -/
theorem chartInvariantOfCoreValues_val :
    (chartInvariantOfCoreValues e I o U hU n a b ha h hcover s w hs).val = s := rfl

end FLT.Mazur.EquivalenceRelationNormalizedFrames
