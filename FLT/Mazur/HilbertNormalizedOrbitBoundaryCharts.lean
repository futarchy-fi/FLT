/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedOrbitBoundaryCoefficients
public import FLT.Mazur.HilbertNormalizedCompleteOrbits

/-!
# Actual affine charts for arbitrary original boundary sections

Every normalized point over an orbit domain has an affine moving chart lifting
all boundary sections on that domain. Every geometric original point has a
complete normalized lift with such a chart. Completeness is asserted at the
lift, not throughout the chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W

/-- An actual affine moving chart lifts every original boundary section on this orbit domain. -/
theorem exists_normalized_orbit_boundary_chart (n : ℕ) (o : Fin n)
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hx : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val) :
    ∃ (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hU : ∀ σ : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
      (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      IsAffineOpen U ∧ x ∈ U ∧
      Etale (U.ι ≫ normalizedFullRelationFirst f hL d V c k n o) ∧
      ∀ t : (invariantSheaf ec).obj.obj (op Wc),
        ∃ a, normalizedBoundaryChartMap f hL d V c k n o U hU a =
          normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t := by
  obtain ⟨U, ha, hxU, hUW, hU, he⟩ := exists_normalized_affine_original_domain
    f hL d V c k n o (pullOpen eo W).val (pullOpen_preimage_eq eo W) x hx
  exact ⟨U, hU, hUW, ha, hxU, he,
    fun t ↦ normalizedOrbitBoundaryCoefficient_lift f hL d V c k n o W U hU hUW t ha⟩

/-- Every geometric original point in the domain has a complete lift with actual affine charts. -/
theorem exists_complete_orbit_boundary_chart {K : Type} [Field K] [IsSepClosed K]
    (a : Spec (.of K) ⟶ A.left) (ha : a default ∈ (pullOpen eo W).val) :
    ∃ (n : ℕ) (o : Fin n)
      (u : Spec (.of K) ⟶ normalizedFullRelationFrames f hL d V c k n o)
      (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hU : ∀ σ : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
      (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      u ≫ normalizedFullRelationFirst f hL d V c k n o = a ∧ Complete (Fin n) o u ∧
      IsAffineOpen U ∧ u default ∈ U ∧
      Etale (U.ι ≫ normalizedFullRelationFirst f hL d V c k n o) ∧
      ∀ t : (invariantSheaf ec).obj.obj (op Wc),
        ∃ v, normalizedBoundaryChartMap f hL d V c k n o U hU v =
          normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t := by
  obtain ⟨n, o, u, hu, hc⟩ :=
    exists_complete_normalized_lift (fullRelationSchemeEquivalence f hL d V c k) a
  change u ≫ normalizedFullRelationFirst f hL d V c k n o = a at hu
  have hx : normalizedFullRelationFirst f hL d V c k n o (u default) ∈
      (pullOpen eo W).val := by
    change (u ≫ normalizedFullRelationFirst f hL d V c k n o) default ∈ _
    rwa [hu]
  obtain ⟨U, hU, hUW, hUa, hxU, he, hl⟩ :=
    exists_normalized_orbit_boundary_chart f hL d V c k W n o (u default) hx
  exact ⟨n, o, u, U, hU, hUW, hu, hc, hUa, hxU, he, hl⟩

end FLT.Mazur.HilbertChart.AffineRestriction
