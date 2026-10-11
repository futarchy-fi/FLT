/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStalkEssentialFiniteType
public import FLT.Mazur.LocalCompletionSmoothCriterion
public import FLT.Mazur.PolygonCompleteAffinePresentation
public import FLT.Mazur.PolygonCompleteNodeStalkCompletion

/-!
# Finiteness and faithful completion at the actual complete node

The actual local ring is Noetherian and essentially of finite type for the
original power-series coefficients. Its completion is faithfully flat and
detects the original cotangent obstructions to formal smoothness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual original power-series map into the complete node stalk is essentially finite type. -/
theorem completeNodeStalkScalars_essFiniteType :
    (completeNodeStalkScalars K n h i U hx).EssFiniteType :=
  AffineClosedPointQuotient.stalkScalars_essFiniteType U ⟨completeNode K n h i, hx⟩
    (completeAffineScalars K n h U) (completeAffineScalars_finiteType K n h U)

/-- The actual maximal-ideal completion is faithfully flat over the actual complete node stalk. -/
theorem completeNodeCompletion_faithfullyFlat :
    Module.FaithfullyFlat
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (IsLocalRing.maximalIdeal
        ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)))
        ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))) :=
  LocalCompletionFaithfullyFlat.faithfullyFlat _

/-- The original cotangent module of the actual complete local stalk is finitely presented. -/
theorem completeNodeDifferentials_finitePresentation :
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    Module.FinitePresentation
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      Ω[(exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)⁄PowerSeries K] := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ : Algebra.EssFiniteType (PowerSeries K)
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)) :=
    completeNodeStalkScalars_essFiniteType K n h i U hx
  exact Module.finitePresentation_of_finite _ _

/-- The local completion gives a faithful test of the actual stalk's cotangent obstructions. -/
theorem completeNode_formallySmooth_iff :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    Algebra.FormallySmooth (PowerSeries K) A ↔
      Module.Flat (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] Ω[A⁄PowerSeries K]) ∧
        Subsingleton (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A]
          Algebra.H1Cotangent (PowerSeries K) A) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ : Algebra.EssFiniteType (PowerSeries K)
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)) :=
    completeNodeStalkScalars_essFiniteType K n h i U hx
  exact LocalCompletionSmoothCriterion.formallySmooth_iff _ _

end FLT.Mazur.PolygonInfinitesimalStages
