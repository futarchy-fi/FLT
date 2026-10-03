/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousClass

/-!
# Coordinatewise continuous cocycles

Product topology makes continuity coordinatewise. Splitting changes also
reconstruct coordinatewise; in particular no exactness premise is needed.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G M ι : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup M] [DistribMulAction G M] [TopologicalSpace M]

/-- Evaluate a product-valued cocycle at one coordinate. -/
def cocycleCoordinate (c : ContinuousCocycle G (ι → M)) (i : ι) :
    ContinuousCocycle G M :=
  ⟨⟨fun g ↦ c.1 g i, (continuous_apply i).comp c.1.continuous⟩,
    fun g h ↦ congrFun (c.2 g h) i⟩

/-- Reconstruct a continuous cocycle from its coordinate cocycles. -/
def cocycleFromCoordinates (c : ι → ContinuousCocycle G M) :
    ContinuousCocycle G (ι → M) :=
  ⟨⟨fun g i ↦ (c i).1 g, continuous_pi fun i ↦ (c i).1.continuous⟩,
    fun g h ↦ funext fun i ↦ (c i).2 g h⟩

/-- Continuous cocycles commute with products of coefficients. -/
def cocycleCoordinatesEquiv :
    ContinuousCocycle G (ι → M) ≃ (ι → ContinuousCocycle G M) where
  toFun := cocycleCoordinate
  invFun := cocycleFromCoordinates
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by funext i; apply Subtype.ext; rfl

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Product-valued splitting changes are exactly coordinatewise splitting changes. -/
theorem splittingEquivalent_coordinates_iff (c d : G → ι → M) :
    SplittingEquivalent c d ↔
      ∀ i, SplittingEquivalent (fun g ↦ c g i) (fun g ↦ d g i) := by
  constructor
  · rintro ⟨a, rfl⟩ i
    exact ⟨a i, rfl⟩
  · intro h
    classical
    choose a ha using h
    exact ⟨a, funext fun g ↦ funext fun i ↦ congrFun (ha i) g⟩

/-- Coordinate reconstruction preserves and reflects continuous splitting classes. -/
theorem cocycleFromCoordinates_equivalent_iff (c d : ι → ContinuousCocycle G M) :
    SplittingEquivalent (fun g ↦ (cocycleFromCoordinates c).1 g)
      (fun g ↦ (cocycleFromCoordinates d).1 g) ↔
        ∀ i, SplittingEquivalent (fun g ↦ (c i).1 g) (fun g ↦ (d i).1 g) :=
  splittingEquivalent_coordinates_iff _ _

end GaloisRepresentation.Extensions
