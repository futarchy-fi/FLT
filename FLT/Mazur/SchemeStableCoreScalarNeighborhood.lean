/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeStableOpenCore
public import FLT.Mazur.SchemeScalarAvoidanceIdeal
public import FLT.Mazur.SchemeOriginalScalarOpenCorrections

/-!
# Stable refinement preserves original scalar neighborhoods

Taking the finite-orbit core of an arbitrary open loses no principal open
cut out by an invariant scalar. Consequently its avoidance ideal and safe
prime locus in the unchanged original scalar ring are exactly the same.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteOrbitOpenCore
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open SchemeScalarPrincipalNeighborhood SchemeFiniteGroupQuotient
variable {G : Type} [Group G] {X : Scheme} (ρ : G →* Aut X)
  (U : X.Opens)
  (hf : (Set.range (fun g : G ↦ (ρ g).hom ⁻¹' (U : Set X))).Finite)

/-- Stable refinement retains every principal neighborhood of an invariant function. -/
theorem basicOpen_le_invariantOpen_iff (r : invariantCoordinates ρ) :
    X.basicOpen r.val ≤ invariantOpen ρ U hf ↔ X.basicOpen r.val ≤ U :=
  ⟨fun h ↦ h.trans (invariantOpen_le ρ U hf),
    fun h ↦ le_invariantOpen ρ U hf _ (basicOpen_stable ρ r) h⟩

variable {R : Type} [CommRing R] (σ : R →+* invariantCoordinates ρ)
local notation "s" => invariantScalarCoordinates ρ σ

/-- The exact original scalar avoidance ideal is unchanged by stable refinement. -/
theorem scalarAvoidanceIdeal_invariantOpen :
    scalarAvoidanceIdeal s (invariantOpen ρ U hf) = scalarAvoidanceIdeal s U := by
  ext r
  rw [mem_scalarAvoidanceIdeal_iff, mem_scalarAvoidanceIdeal_iff]
  exact basicOpen_le_invariantOpen_iff ρ U hf (σ r)

/-- Every original safe prime survives, without any integrality or affineness assumption. -/
theorem scalarNeighborhoodLocus_invariantOpen :
    scalarNeighborhoodLocus s (invariantOpen ρ U hf) = scalarNeighborhoodLocus s U := by
  apply SetLike.coe_injective
  ext P
  change P ∈ scalarNeighborhoodLocus s (invariantOpen ρ U hf) ↔
    P ∈ scalarNeighborhoodLocus s U
  rw [mem_scalarNeighborhoodLocus_iff_not_le, mem_scalarNeighborhoodLocus_iff_not_le,
    scalarAvoidanceIdeal_invariantOpen]

/-- An original safe prime constructs a principal neighborhood inside the stable core. -/
theorem exists_scalar_invariantOpen (P : PrimeSpectrum R)
    (hP : P ∈ scalarNeighborhoodLocus s U) :
    ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (σ r).val ≤ invariantOpen ρ U hf := by
  obtain ⟨r, hr, hU⟩ := (mem_scalarNeighborhoodLocus_iff s U P).mp hP
  exact ⟨r, hr, (basicOpen_le_invariantOpen_iff ρ U hf (σ r)).mpr hU⟩

end FLT.Mazur.SchemeFiniteOrbitOpenCore
