/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteInteriorCharts
public import FLT.Mazur.EquivalenceRelationCompleteMixedCoefficients

/-!
# Original boundary lifts with full compatibility on complete interior charts

The constructed complete affine neighborhoods lift every original boundary
section to a coefficient satisfying the entire self-mixed original relation.
This does not identify separately chosen lifts on independent charts.
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
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W

/-- Interior completeness constructs actual boundary lifts with full chart self-compatibility. -/
theorem exists_completeInterior_boundary_lifts (n : ℕ) (o : Fin n)
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hx : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val)
    (hc : x ∈ completeInterior («p» := p) («q» := q) (Fin n) o) :
    ∃ (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hU : ∀ σ : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
      (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      IsAffineOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) ∧
      ∀ t : (invariantSheaf ec).obj.obj (op Wc),
        ∃ a, normalizedBoundaryChartMap f hL d V c k n o U hU a =
          normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t ∧
          (MixedFrames.mixedChartFirst o o U U).appTop a.val =
            (MixedFrames.mixedChartSecond o o U U).appTop a.val := by
  obtain ⟨U, hU, hUW, ha, hxU, hcomplete, _⟩ :=
    exists_completeInterior_orbit_chart f hL d V c k W n o x hx hc
  refine ⟨U, hU, hUW, ha, hxU, hcomplete, ?_⟩
  intro t
  obtain ⟨a, ha⟩ := normalizedOrbitBoundaryCoefficient_lift f hL d V c k n o W U hU hUW t ha
  exact ⟨a, ha, completeOpen_invariant_mixed e (Fin n) o U hU hcomplete a⟩

end FLT.Mazur.HilbertChart.AffineRestriction
