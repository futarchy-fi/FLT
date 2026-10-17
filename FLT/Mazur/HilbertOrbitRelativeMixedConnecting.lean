/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitRelativeMixedError
public import FLT.Mazur.RelativeBoundaryConnectingMap

/-!
# The relative mixed obstruction is a linear connecting map

The actual chosen chart lifts give a canonical linear map to the exact relative
mixed quotient. Its kernel is precisely the original invariant restrictions,
so the quotient of boundary sections embeds in the relative mixed obstruction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency true
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

attribute [local irreducible] originalChartScalarMap
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "Ac" => chartCoordinateRing f hL d V c k W hW
local notation "Bc" => chartBoundaryCoordinateRing f hL d V c k W hW
local notation "Cc" => mixedCoordinateRing f hL d V c k W hW

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "D" => (invariantSheaf ec).obj.obj (op Wc)
local notation "ρ" => originalClosedSectionPullback f hL d V c k W

attribute [local instance] originalBoundarySectionAlgebra originalCorrectionBoundaryAlgebra
  originalCorrectionChartAlgebra originalCorrectionMixedAlgebra
attribute [local irreducible] originalBoundaryCoefficientLinearMap
  BoundaryCorrectionIdeal.originalCorrectionOperator
  originalCorrectionBoundaryHom originalCorrectionFirstHom originalCorrectionSecondHom
local notation "Hb" => originalCorrectionBoundaryHom f hL d V c k W hW
local notation "Fp" => originalCorrectionFirstHom f hL d V c k W hW
local notation "Gq" => originalCorrectionSecondHom f hL d V c k W hW
local notation "β" => originalBoundaryCoefficientLinearMap f hL d V c k W hW
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "n" => fun j : Charts ↦ j.val.size
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "Cmix" => (∀ j l : Charts, Cc j l)

attribute [local irreducible] originalMixedBoundaryKernel originalBoundaryMixedCorrectionImage
local notation "N" => originalMixedBoundaryKernel f hL d V c k W hW
local notation "K" => originalBoundaryMixedCorrectionImage f hL d V c k W hW

/-- The original boundary obstruction valued in the exact mixed boundary quotient. -/
def originalRelativeMixedConnectingMap : D →ₗ[Ω] N ⧸ (K).comap (N).subtype := by
  unfold originalBoundaryMixedCorrectionImage
  exact RelativeBoundaryConnectingMap.connecting
    (BoundaryCorrectionIdeal.boundaryCoordinates Hb)
    (BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq) N β
    (lifts f hL d V c k W hW)
    (originalBoundaryCoefficientLinearMap_lifts f hL d V c k W hW)
    (originalLiftDiscrepancy_mem_boundary f hL d V c k W hW)

/-- The constructed linear map has exactly the previously defined actual relative error. -/
theorem originalRelativeMixedConnectingMap_apply (t : D) :
    originalRelativeMixedConnectingMap f hL d V c k W hW t =
      originalRelativeMixedError f hL d V c k W hW t := by
  unfold originalRelativeMixedConnectingMap originalRelativeMixedError
    RelativeBoundaryConnectingMap.connecting RelativeBoundaryConnectingMap.relativeClass
    originalBoundaryMixedCorrectionImage BoundaryCorrectionIdeal.mixedCorrectionImage
  rfl

attribute [local irreducible] originalRelativeMixedConnectingMap
  originalRelativeMixedError originalBoundaryObstructionMap

/-- Relative vanishing constructs the same full original lift as the original obstruction. -/
theorem originalRelativeMixedConnectingMap_eq_zero_iff (t : D) :
    originalRelativeMixedConnectingMap f hL d V c k W hW t = 0 ↔
      originalBoundaryObstructionMap f hL d V c k W hW t = 0 := by
  unfold originalRelativeMixedConnectingMap originalBoundaryObstructionMap
  unfold originalBoundaryMixedCorrectionImage
  refine (RelativeBoundaryConnectingMap.connecting_eq_zero_iff
    (BoundaryCorrectionIdeal.boundaryCoordinates Hb)
    (BoundaryCorrectionIdeal.mixedDiscrepancy Fp Gq) N β
    (lifts f hL d V c k W hW)
    (originalBoundaryCoefficientLinearMap_lifts f hL d V c k W hW)
    (originalLiftDiscrepancy_mem_boundary f hL d V c k W hW) t).trans ?_
  rw [BoundaryCorrectionIdeal.originalBoundaryCokernelMap_eq_zero_iff]
  constructor
  · rintro ⟨v, hb, hd⟩
    exact ⟨v, congrFun hb, fun j l ↦ sub_eq_zero.mp (congrFun (congrFun hd j) l)⟩
  · rintro ⟨v, hb, hd⟩
    exact ⟨v, funext hb, by funext j l; exact sub_eq_zero.mpr (hd j l)⟩

/-- The relative connecting kernel retains exactly the original invariant restrictions. -/
theorem originalRelativeMixedConnectingMap_ker :
    LinearMap.ker (originalRelativeMixedConnectingMap f hL d V c k W hW) =
      LinearMap.range (originalBoundaryPullbackLinearMap f hL d V c k W) := by
  rw [← originalBoundaryObstruction_ker f hL d V c k W hW]
  ext t
  exact originalRelativeMixedConnectingMap_eq_zero_iff f hL d V c k W hW t

/-- Original boundary sections modulo original restrictions are exactly the relative error image. -/
def originalRelativeMixedImageEquiv :
    (D ⧸ LinearMap.range (originalBoundaryPullbackLinearMap f hL d V c k W)) ≃ₗ[Ω]
      LinearMap.range (originalRelativeMixedConnectingMap f hL d V c k W hW) :=
  (Submodule.quotEquivOfEq _ _
    (originalRelativeMixedConnectingMap_ker f hL d V c k W hW).symm).trans
      (originalRelativeMixedConnectingMap f hL d V c k W hW).quotKerEquivRange

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
