/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLinearSystem

/-!
# The actual boundary coefficient homomorphism

The original boundary section ring acts through its exact chart coefficients.
These maps are linear over original invariant scalars and use no chosen lifts.
No finite generation of the boundary section module is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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

/-- Original scalars act on boundary sections by the actual closed pullback. -/
@[instance_reducible]
def originalBoundarySectionAlgebra : Algebra Ω D := (ρ).toAlgebra

attribute [local instance] originalBoundarySectionAlgebra originalCorrectionBoundaryAlgebra
  originalCorrectionChartAlgebra originalCorrectionMixedAlgebra

/-- Exact chart coefficients form a ring homomorphism on original boundary sections. -/
def originalBoundaryCoefficientRingHom (j : Charts) : D →+* Bc j := by
  let sourceMap : D →+* Γ((pullOpen ec Wc).val.toScheme, ⊤) :=
    { toFun := fun x ↦ (orbitFunctions ec Wc x).val
      map_zero' := congrArg Subtype.val (map_zero (orbitFunctions ec Wc))
      map_one' := congrArg Subtype.val (map_one (orbitFunctions ec Wc))
      map_add' := fun x y ↦ congrArg Subtype.val (map_add (orbitFunctions ec Wc) x y)
      map_mul' := fun x y ↦ congrArg Subtype.val (map_mul (orbitFunctions ec Wc) x y) }
  let coeffMap :=
    ((normalizedOriginalBoundaryEndpoint f hL d V c k j.val.size j.val.label).resLE
      (pullOpen ec Wc).val
      (normalizedOriginalBoundaryInclusion f hL d V c k j.val.size j.val.label ⁻¹ᵁ j.val.domain)
      (normalizedOrbitBoundary_domain_le f hL d V c k j.val.size j.val.label W j.val.domain
        j.val.overDomain)).appTop.hom.comp sourceMap
  exact
    { toFun := normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain
      map_zero' := by
        apply Subtype.ext
        simp only [normalizedOrbitBoundaryCoefficient_val]
        exact map_zero coeffMap
      map_one' := by
        apply Subtype.ext
        simp only [normalizedOrbitBoundaryCoefficient_val]
        exact map_one coeffMap
      map_add' := fun x y ↦ by
        apply Subtype.ext
        change _ =
          (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
            j.val.domain j.val.stable j.val.overDomain x).val +
          (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
            j.val.domain j.val.stable j.val.overDomain y).val
        simp only [normalizedOrbitBoundaryCoefficient_val]
        exact map_add coeffMap x y
      map_mul' := fun x y ↦ by
        apply Subtype.ext
        change _ =
          (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
            j.val.domain j.val.stable j.val.overDomain x).val *
          (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
            j.val.domain j.val.stable j.val.overDomain y).val
        simp only [normalizedOrbitBoundaryCoefficient_val]
        exact map_mul coeffMap x y }

/-- Evaluation of the ring map is the original chart coefficient. -/
theorem originalBoundaryCoefficientRingHom_apply (j : Charts) (t : D) :
    originalBoundaryCoefficientRingHom f hL d V c k W hW j t =
      normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t := rfl

attribute [local irreducible] originalBoundaryCoefficientRingHom

/-- Chart coefficients commute with the original scalar pullback. -/
def originalBoundaryCoefficientAlgHom (j : Charts) : D →ₐ[Ω] Bc j where
  __ := originalBoundaryCoefficientRingHom f hL d V c k W hW j
  commutes' a := by
    change originalBoundaryCoefficientRingHom f hL d V c k W hW j (ρ a) = _
    rw [originalBoundaryCoefficientRingHom_apply]
    exact (originalChartScalarMap_boundary f hL d V c k W hW a j).symm

attribute [local irreducible] originalBoundaryCoefficientAlgHom

/-- All exact chart boundary values, packaged as one linear coefficient map. -/
def originalBoundaryCoefficientLinearMap : D →ₗ[Ω] (∀ j : Charts, Bc j) :=
  LinearMap.pi fun j ↦ (originalBoundaryCoefficientAlgHom f hL d V c k W hW j).toLinearMap

attribute [local irreducible] originalBoundaryCoefficientLinearMap

/-- Evaluation recovers the unchanged original boundary coefficient. -/
theorem originalBoundaryCoefficientLinearMap_apply (t : D) (j : Charts) :
    originalBoundaryCoefficientLinearMap f hL d V c k W hW t j =
      normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t := by
  unfold originalBoundaryCoefficientLinearMap originalBoundaryCoefficientAlgHom
  change originalBoundaryCoefficientRingHom f hL d V c k W hW j t = _
  exact originalBoundaryCoefficientRingHom_apply f hL d V c k W hW j t

/-- Chosen chart lifts have exactly the values of the linear boundary coefficient map. -/
theorem originalBoundaryCoefficientLinearMap_lifts (t : D) :
    (fun j ↦ originalCorrectionBoundaryHom f hL d V c k W hW j
      (lifts f hL d V c k W hW t j)) =
        originalBoundaryCoefficientLinearMap f hL d V c k W hW t := by
  funext j
  rw [originalBoundaryCoefficientLinearMap_apply]
  exact lifts_restrict f hL d V c k W hW t j

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
