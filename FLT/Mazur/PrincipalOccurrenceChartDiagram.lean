/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceGluingAffineLimit
public import FLT.Mazur.PrincipalOccurrenceGluedCartesian
/-!
# Cartesian inclusions of affine chart diagrams

The literal glued-chart inclusions assemble into a natural transformation
from each affine inverse diagram to the global inverse diagram. Its squares
are cartesian, retaining the actual stage and target labels.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Small.{u} ι]

/-- The inclusions of one whole chart form a map of inverse diagrams. -/
def principalOccurrenceChartInclusion (i : Shrink.{u} ι) :
    principalOccurrenceGluingAffineDiagram e ((equivShrink.{u} ι).symm i) ⟶
      principalOccurrenceGluedDiagram e where
  app x := (principalOccurrenceStageGlueData e x.unop).ι i
  naturality x y g := by
    have h := principalOccurrenceGluedTransition_chart e y.unop x.unop
      (leOfHom g.unop) i
    unfold principalOccurrenceGluingChartMap at h
    exact h.symm

/-- Every component is the open embedding of a literal glued chart. -/
instance principalOccurrenceChartInclusion_isOpenImmersion (i : Shrink.{u} ι)
    (x : (PrincipalOccurrenceGluingStage e)ᵒᵖ) :
    IsOpenImmersion ((principalOccurrenceChartInclusion e i).app x) :=
  (principalOccurrenceStageGlueData e x.unop).ι_isOpenImmersion i

/-- Every square of a chart inclusion is cartesian. -/
theorem principalOccurrenceChartInclusion_isPullback (i : Shrink.{u} ι)
    {x y : (PrincipalOccurrenceGluingStage e)ᵒᵖ} (g : x ⟶ y) :
    IsPullback ((principalOccurrenceGluingAffineDiagram e ((equivShrink.{u} ι).symm i)).map g)
      ((principalOccurrenceChartInclusion e i).app x)
      ((principalOccurrenceChartInclusion e i).app y)
      ((principalOccurrenceGluedDiagram e).map g) := by
  have h := principalOccurrenceGluedTransition_isPullback e y.unop x.unop
    (leOfHom g.unop) i
  unfold principalOccurrenceGluingChartMap at h
  exact h

end FLT.Mazur.FiniteTypeRelationModel
