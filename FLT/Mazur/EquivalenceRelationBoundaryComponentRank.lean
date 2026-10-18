/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryExcess
public import FLT.Mazur.SchemeFiniteGroupBoundaryComponents

/-!
# Exact original rank tests on minimal boundary components

Excess emptiness is equivalent to exact rank at a lift of each minimal
component of the actual scalar boundary product. Failure has an actual larger
original frame at that component's unchanged boundary prime. No finite-locus
assumption or reduction of the original product is introduced.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples SchemeScalarPrincipalNeighborhood AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction invariantScalarCoordinates
  boundaryProduct boundaryCoordinate boundaryComponentPoint closedOrbitTests componentBoundaryPrime
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] [NoetherianSpace U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local instance componentRankOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance componentRankOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance componentRankOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o

omit [IsAffine U.toScheme] [NoetherianSpace U.toScheme] in
/-- At an original chart point, completeness means its exact rank is the frame size. -/
theorem chart_complete_iff_exactRank (x : U.toScheme) :
    x ∈ Z ↔ first p q (Fin n) o (U.ι x) ∈ exactRank (Over.mk p) n := by
  rw [completePointLocus_eq_rankAtMost_preimage]
  exact ⟨fun h ↦ ⟨⟨inclusion p q (Fin n) o (U.ι x), rfl⟩, h⟩, fun h ↦ h.2⟩

/-- Excess emptiness is tested at one original exact-rank lift of each minimal component. -/
theorem boundaryExcess_empty_iff_component_exactRank :
    IsEmpty (boundaryExcess n o U (invariantScalarCoordinates ρ s) κ) ↔
      ∀ Q : minimalPrimes C, ∃ x : U.toScheme,
        quotientMap ρ x = boundaryProjection s κ (boundaryComponentPoint s κ Q) ∧
        first p q (Fin n) o (U.ι x) ∈ exactRank (Over.mk p) n := by
  refine (boundaryExcess_isEmpty_iff n o U (invariantScalarCoordinates ρ s) κ).trans ?_
  refine (all_scalar_fibers_subset_iff_component_lifts ρ Z
    (completeChart_isClosed (Fin n) o U) (completeChart_stable e (Fin n) o U hU) s κ).trans ?_
  simp_rw [chart_complete_iff_exactRank]

/-- Every original chart lift of a failed component equation has a larger original frame. -/
theorem boundary_component_lift_excess_frame
    (b : invariantCoordinates ρ) (hb : b ∈ completeAffineOrbitTests e (Fin n) o U hU)
    (Q : minimalPrimes C) (hQ : Ideal.Quotient.mk Q.val (boundaryCoordinate s κ b) ≠ 0)
    (x : U.toScheme)
    (hx : quotientMap ρ x = boundaryProjection s κ (boundaryComponentPoint s κ Q)) :
    ∃ y : (distinctScheme (Over.mk p) (Fin (n + 1))).left,
      (distinctScheme (Over.mk p) (Fin (n + 1))).hom y = first p q (Fin n) o (U.ι x) := by
  apply (not_completePoint_iff_larger_frame n o (U.ι x)).mp
  intro hz
  exact hQ ((component_equations_iff_closed_image ρ Z
    (completeChart_isClosed (Fin n) o U) s κ Q).mpr ⟨x, hz, hx⟩ b hb)

/-- Exact-rank component lifts yield simultaneous equations in the full nonreduced product. -/
theorem boundary_power_of_component_exactRank
    (h : ∀ Q : minimalPrimes C, ∃ x : U.toScheme,
      quotientMap ρ x = boundaryProjection s κ (boundaryComponentPoint s κ Q) ∧
      first p q (Fin n) o (U.ι x) ∈ exactRank (Over.mk p) n) :
    ∃ N : ℕ, ∀ b ∈ completeAffineOrbitTests e (Fin n) o U hU,
      boundaryCoordinate s κ b ^ N = 0 := by
  apply (all_scalar_fibers_subset_iff_boundary_power ρ Z
    (completeChart_isClosed (Fin n) o U) (completeChart_stable e (Fin n) o U hU) s κ).mp
  exact (boundaryExcess_isEmpty_iff n o U (invariantScalarCoordinates ρ s) κ).mp
    ((boundaryExcess_empty_iff_component_exactRank n o U e hU s κ).mpr h)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
