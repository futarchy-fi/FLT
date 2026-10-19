/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryScalarRanks
public import FLT.Mazur.EquivalenceRelationBoundaryPrincipalCharts

/-!
# Faithful matching charts over genuine original scalar neighborhoods

A scalar power certificate gives a faithful chart over the entire inverse
image of a scalar principal open, with full matching-stage recovery. Every
prime in the scalar nilpotence open has such a chart around it.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local notation "π" => chartBoundaryProduct n o U e hU s κ
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local instance scalarChartOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarChartOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarChartOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
variable (t : T)
local notation "u" => boundaryScalarHom s κ t
local notation "V" => (boundaryProduct s κ).basicOpen u

omit [Etale p] [QuasiCompact p] [IsAffine U.toScheme] in
/-- The coefficient neighborhood is the whole inverse image of the original scalar open. -/
theorem boundary_scalar_principal_range :
    Set.range (V).ι = boundaryScalarProjection s κ ⁻¹'
      (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum T)) := by
  rw [Scheme.Opens.range_ι, boundaryScalarHom_basicOpen]
  rfl

omit [Etale p] [QuasiCompact p] in
/-- The faithful chart covers every original product point over the chosen scalar neighborhood. -/
theorem boundary_scalar_principal_chart_range :
    Set.range (boundaryPrincipalProjection n o U e hU s κ u ≫ (V).ι) =
      boundaryScalarProjection s κ ⁻¹'
        (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum T)) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (show Function.Surjective (boundaryPrincipalProjection n o U e hU s κ u) from
      (inferInstance : Surjective (boundaryPrincipalProjection n o U e hU s κ u)).1).range_eq,
    Set.image_univ, boundary_scalar_principal_range]

variable [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
local notation "I" => boundaryTestIdeal s κ tests
attribute [local irreducible] completeAffineOrbitTests boundaryTestIdeal
  boundaryPrincipalProjection boundaryPrincipalEndpoint

/-- A genuine scalar power certificate makes every point above that scalar open matching. -/
theorem boundary_scalar_principal_rank (order : ℕ)
    (ht : u ∈ (I ^ order).annihilator) (z : boundaryProduct s κ)
    (hz : t ∉ (boundaryScalarProjection s κ z).asIdeal) :
    boundaryPointRank n o U e hU s κ z = n := by
  apply boundary_rank_eq_of_power_annihilator n o U e hU s κ order u ht z
  change t ∉ (((boundaryProduct s κ).isoSpec.hom z).asIdeal).comap (boundaryScalarHom s κ)
  rwa [boundaryScalarHom_comap_point]

/-- Scalar power certificates split the full relation on the corresponding faithful chart. -/
theorem boundary_scalar_principal_complete_frames (order : ℕ)
    (ht : u ∈ (I ^ order).annihilator) :
    Function.Surjective (rankFrameProjection (Over.mk p) n
      (boundaryPrincipalEndpoint n o U e hU s κ u)) :=
  boundaryPrincipal_complete_frame_surjective n o U e hU s κ u order ht

variable [AlgebraicGeometry.IsNoetherian A]

/-- Each original scalar prime in the constructed open has a faithful matching-stage chart. -/
theorem exists_boundary_scalar_rank_chart (P : PrimeSpectrum T)
    (hP : P ∈ boundaryScalarNilpotenceOpen s κ tests) :
    ∃ t : T, t ∉ P.asIdeal ∧ ∃ stage : ℕ,
      IsIso (rankPullbackMap (Over.mk p)
        (boundaryPrincipalEndpoint n o U e hU s κ (boundaryScalarHom s κ t)) n stage) := by
  obtain ⟨order, t, ht, ha⟩ := (mem_boundaryScalarNilpotenceOpen s κ tests P).mp hP
  exact ⟨t, ht, boundaryPrincipal_rank_recovery n o U e hU s κ
    (boundaryScalarHom s κ t) order ha⟩

/-- Matching generizing component ranks produce a chart without choosing a product denominator. -/
theorem exists_boundary_scalar_rank_chart_of_components (P : PrimeSpectrum T)
    (hP : ∀ Q : minimalPrimes C,
      (boundaryScalarProjection s κ (boundaryComponentPoint s κ Q)).asIdeal ≤ P.asIdeal →
        boundaryPointRank n o U e hU s κ (boundaryComponentPoint s κ Q) = n) :
    ∃ t : T, t ∉ P.asIdeal ∧ ∃ stage : ℕ,
      IsIso (rankPullbackMap (Over.mk p)
        (boundaryPrincipalEndpoint n o U e hU s κ (boundaryScalarHom s κ t)) n stage) :=
  exists_boundary_scalar_rank_chart n o U e hU s κ P
    ((mem_boundaryScalarNilpotenceOpen_iff_matching_components n o U e hU s κ P).mpr hP)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
