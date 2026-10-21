/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankCollisionConstructible

/-!
# Exact generizing-point tests for the scalar rank obstruction

The closure of the collision image has actual collision witnesses above
scalar generizations. Thus common rank over the whole scalar localization
constructs a principal neighborhood. A single scalar fiber is insufficient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] [NoetherianSpace A] [CompactSpace T] [QuasiSeparatedSpace T]
  (x y : T ⟶ A) [QuasiCompact x] [QuasiCompact y]
  {R : Type} [CommRing R] (s : T ⟶ Spec (.of R)) [QuasiCompact s]

/-- Every original scalar closure point has an actual collision over a generizing prime. -/
theorem mem_rankCollision_image_closure_iff (P : PrimeSpectrum R) :
    P ∈ closure (s '' rankCollision E x y) ↔
      ∃ t ∈ rankCollision E x y, (s t).asIdeal ≤ P.asIdeal := by
  rw [ConstructibleImageGenerizations.mem_closure_image_iff s s.isSpectralMap
    (rankCollision_constructibly_compact E x y)]
  exact exists_congr fun t ↦ and_congr_right fun _ ↦
    (PrimeSpectrum.le_iff_specializes (s t) P).symm

/-- The obstruction ideal detects actual generizing collisions, not hypothetical closure points. -/
theorem rankCollisionIdeal_le_iff_generizing_collision (P : PrimeSpectrum R) :
    rankCollisionIdeal E x y s ≤ P.asIdeal ↔
      ∃ t ∈ rankCollision E x y, (s t).asIdeal ≤ P.asIdeal := by
  change P ∈ PrimeSpectrum.zeroLocus (rankCollisionIdeal E x y s : Set R) ↔ _
  rw [rankCollisionIdeal_zeroLocus, mem_rankCollision_image_closure_iff]

/-- Common rank over all generizing original primes is the exact neighborhood criterion. -/
theorem rankCollisionIdeal_not_le_iff_generizing_ranks (P : PrimeSpectrum R) :
    ¬ rankCollisionIdeal E x y s ≤ P.asIdeal ↔
      ∀ t : T, (s t).asIdeal ≤ P.asIdeal →
        ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n := by
  rw [rankCollisionIdeal_le_iff_generizing_collision]
  constructor
  · intro h t ht
    exact (not_mem_rankCollision_iff E x y t).mp (fun hc ↦ h ⟨t, hc, ht⟩)
  · rintro h ⟨t, hc, ht⟩
    exact (not_mem_rankCollision_iff E x y t).mpr (h t ht) hc

/-- Control of the whole original localization constructs one original principal denominator. -/
theorem exists_same_rank_principal_of_generizing_ranks (P : PrimeSpectrum R)
    (h : ∀ t : T, (s t).asIdeal ≤ P.asIdeal →
      ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n) :
    ∃ r : R, r ∉ P.asIdeal ∧
      ∀ t : T, s t ∈ PrimeSpectrum.basicOpen r →
        ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n :=
  (rankCollisionIdeal_not_le_iff E x y s P).mp
    ((rankCollisionIdeal_not_le_iff_generizing_ranks E x y s P).mpr h)

/-- Specialization stability is sufficient for actual collision-image closedness. -/
theorem rankCollision_image_isClosed_of_stable
    (h : StableUnderSpecialization (s '' rankCollision E x y)) :
    IsClosed (s '' rankCollision E x y) := by
  apply isClosed_of_closure_subset
  intro P hP
  obtain ⟨t, ht, htP⟩ := (mem_rankCollision_image_closure_iff E x y s P).mp hP
  exact h ((PrimeSpectrum.le_iff_specializes _ _).mp htP) ⟨t, ht, rfl⟩

end FLT.Mazur.RelativeOrderedTuples
