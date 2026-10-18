/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLinearSystem
public import FLT.Mazur.HilbertMixedResidualBranches
public import FLT.Mazur.EquivalenceRelationMixedResidualScalars

/-!
# Split residual coefficients on the fixed original Hilbert atlas

The residual maps use the unchanged original invariant scalar ring and each
full independently indexed mixed relation. The splitting proves injective
reduction of the residual summand on this actual atlas; it does not yet split
the original mixed boundary kernel or construct a boundary-zero correction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source
namespace OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] finiteCharts lifts obstruction
  scalarFamily normalizedBoundaryChartMap normalizedOrbitBoundaryCoefficient
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

attribute [local instance] originalCorrectionMixedAlgebra
local instance originalResidual_sourceSeparated (n : ℕ) (o : Fin n) :
    (source (fst f hL d V c k).left (snd f hL d V c k).left (Fin n) o).IsSeparated :=
  normalizedFrameSource_separated f hL d V c k n o

/-- The actual residual open of a full mixed relation on the fixed original atlas. -/
def originalMixedResidualOpen (j l : Charts) :
    (MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).toScheme.Opens :=
  MixedFrames.mixedResidualTestOpen ef j.val.label l.val.label
    (MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).ι

/-- Its coefficient ring retains every original residual nilpotent. -/
abbrev originalMixedResidualRing (j l : Charts) : Type :=
  Γ((originalMixedResidualOpen f hL d V c k W hW j l).toScheme, ⊤)

/-- Original invariant scalars act through the actual full mixed restriction. -/
@[instance_reducible] def originalMixedResidualAlgebra (j l : Charts) :
    Algebra Ω (originalMixedResidualRing f hL d V c k W hW j l) :=
  MixedFrames.mixedResidualCoefficientAlgebra ef j.val.label l.val.label
    (MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).ι Ω
attribute [local instance] originalMixedResidualAlgebra

/-- Actual residual coefficients extend linearly to the entire original mixed coefficient ring. -/
def originalMixedResidualExtension (j l : Charts) :
    originalMixedResidualRing f hL d V c k W hW j l →ₗ[Ω] Cc j l :=
  MixedFrames.mixedResidualSectionLinearExtension ef j.val.label l.val.label
    (MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).ι Ω

/-- Actual residual restriction uses the same unchanged original scalars. -/
def originalMixedResidualRestriction (j l : Charts) :
    Cc j l →ₗ[Ω] originalMixedResidualRing f hL d V c k W hW j l :=
  MixedFrames.mixedResidualSectionLinearRestriction ef j.val.label l.val.label
    (MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).ι Ω

/-- The fixed original atlas has a constructed splitting on every independent mixed pair. -/
theorem originalMixedResidual_split (j l : Charts) :
    (originalMixedResidualRestriction f hL d V c k W hW j l).comp
      (originalMixedResidualExtension f hL d V c k W hW j l) = LinearMap.id :=
  MixedFrames.mixedResidualSectionLinear_split ef j.val.label l.val.label
    (MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).ι Ω

/-- Every scalar ideal has injective reduction on each actual residual-supported summand. -/
theorem originalMixedResidual_reduction_injective (J : Ideal Ω) (j l : Charts) :
    Function.Injective (SubmoduleReduction.inclusion J
      (LinearMap.range (originalMixedResidualExtension f hL d V c k W hW j l))) :=
  SplitSubmoduleReduction.reduced_range_injective _ _
    (originalMixedResidual_split f hL d V c k W hW j l) J

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
