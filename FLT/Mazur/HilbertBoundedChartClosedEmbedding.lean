/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedNormalizedCoordinates
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed embeddings of bounded Hilbert charts in normalized coordinate spaces

Each original monomial Hilbert chart is a closed subscheme of the normalized
bounded-coordinate space. Its equation ideal is the full kernel of the
surjective coordinate map. Identifying this target with the appropriate
Grassmannian chart and identifying its global pullback remain separate steps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)

/-- All equations of the original Hilbert chart in normalized bounded coordinates. -/
def boundedHilbertChartEquationIdeal : Ideal (BoundedNormalizedRing R I d m) :=
  RingHom.ker (chartNormalizedCoordinateMap R I d m).toRingHom

/-- Quotienting by every coordinate equation recovers the entire original chart ring. -/
def boundedHilbertChartCoordinateEquiv :
    (BoundedNormalizedRing R I d m ⧸ boundedHilbertChartEquationIdeal R I d m) ≃ₐ[R]
      ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1) :=
  Ideal.quotientKerAlgEquivOfSurjective (chartNormalizedCoordinateMap_surjective R I d m)

/-- The complete closed coordinate locus uses the original coefficient base. -/
def boundedNormalizedScheme : Scheme.{u} := Spec (.of (BoundedNormalizedRing R I d m))

/-- The constructed morphism from the actual monomial Hilbert chart. -/
def boundedHilbertChartClosedMap :
    Spec (.of (ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1))) ⟶
      boundedNormalizedScheme R I d m :=
  Spec.map (CommRingCat.ofHom (chartNormalizedCoordinateMap R I d m).toRingHom)

/-- The bounded Hilbert chart morphism is a genuine closed immersion. -/
instance boundedHilbertChartClosedMap_isClosedImmersion :
    IsClosedImmersion (boundedHilbertChartClosedMap R I d m) :=
  IsClosedImmersion.spec_of_surjective _ (chartNormalizedCoordinateMap_surjective R I d m)

/-- The actual closed immersion lies over the unchanged original coefficient ring. -/
theorem boundedHilbertChartClosedMap_over :
    boundedHilbertChartClosedMap R I d m ≫
        Spec.algebraMap R (BoundedNormalizedRing R I d m) =
      Spec.algebraMap R (ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1)) := by
  rw [boundedHilbertChartClosedMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    (AlgHom.comp_algebraMap (chartNormalizedCoordinateMap R I d m))

/-- Equality of every retained equation characterizes factoring a coefficient map. -/
theorem boundedHilbertChart_equations_iff {S : Type u} [CommRing S] [Algebra R S]
    (f : BoundedNormalizedRing R I d m →ₐ[R] S) :
    boundedHilbertChartEquationIdeal R I d m ≤ RingHom.ker f.toRingHom ↔
      ∃ g : ChartRing R I d (fun a ↦ MvPolynomial.monomial (m a).val 1) →ₐ[R] S,
        g.comp (chartNormalizedCoordinateMap R I d m) = f := by
  constructor
  · intro h
    let q := Ideal.Quotient.liftₐ _ f h
    refine ⟨q.comp (boundedHilbertChartCoordinateEquiv R I d m).symm.toAlgHom, ?_⟩
    apply AlgHom.ext
    intro z
    change q ((boundedHilbertChartCoordinateEquiv R I d m).symm
      (chartNormalizedCoordinateMap R I d m z)) = f z
    have hz : (boundedHilbertChartCoordinateEquiv R I d m)
        (Ideal.Quotient.mk _ z) = chartNormalizedCoordinateMap R I d m z := rfl
    rw [← hz, AlgEquiv.symm_apply_apply]
    rfl
  · rintro ⟨g, rfl⟩ z hz
    change g (chartNormalizedCoordinateMap R I d m z) = 0
    change chartNormalizedCoordinateMap R I d m z = 0 at hz
    rw [hz, map_zero]

end FLT.Mazur.HilbertChart
