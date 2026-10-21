/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryUniformFlatRelation
public import FLT.Mazur.RankStageCoreCorrectionSpace

/-!
# Uniform whole-core rank corrections from a flat scalar branch

The exponent is chosen before the boundary, numerator, rank and chart family.
Only full branch equations are supplied. Original boundary lift ideals feed
the whole-core correction ideal in the proved forward direction, preserving
all original boundary and mixed equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A Y : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance uniformFlatOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance uniformFlatOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance uniformFlatOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCoreCorrectionIdeal
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))
variable (g : Y ⟶ Spec (.of (compatibleFunctions p q)))
  [Flat g] [LocallyOfFinitePresentation g] (V : Y.Opens)
local notation "π" => scalarMorphism σD
local notation "k" => pullback.fst π g
local notation "h" => pullback.snd π g
local notation "O" => scalarBranchSolutionOpen σD g V

/-- A common flat branch gives one original ideal power for every whole-core rank correction. -/
theorem exists_pow_le_all_rankStageCorrectionIdeals_of_flat_branch
    (Q : Ideal (compatibleFunctions p q)) (hfg : Q.FG)
    (hQ : Q ≤ scalarAvoidanceIdeal σD O) :
    ∃ N : ℕ, ∀ (J : A.IdealSheafData) (a : Γ(A, ⊤)),
      (pullback π g : Scheme).presheaf.map
        (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op
          ((k).appTop (p.appTop a - q.appTop a)) = 0 →
      ∀ (n : ℕ) (ι : Type) (c : ι → Γ(A, ⊤))
        (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
        (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)),
        (∀ j l, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J l).subschemeι.appTop
          ((v j).val l).val = (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J l).appTop
            (J.subschemeι.appTop a)) →
        Q ^ N ≤ rankStageCoreCorrectionIdeal e n c hc J v := by
  let _ : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian p
  let _ := QuasiCompact.compactSpace_of_compactSpace p
  let _ : IsNoetherian D := ⟨⟩
  obtain ⟨N, hN⟩ := exists_pow_le_originalBoundaryLiftIdeals_of_flat_branch g V Q hfg hQ
  refine ⟨N, fun J a ha n _ c hc v hv ↦ ?_⟩
  exact (hN J a ha).trans (originalBoundaryLiftIdeal_le_correctionIdeal J
    (J.subschemeι.appTop a) e n c hc v hv)

end FLT.Mazur.EquivalenceRelationOrderedFrames
