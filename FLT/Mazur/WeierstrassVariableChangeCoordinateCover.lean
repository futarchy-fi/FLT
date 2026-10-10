/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeHomogeneous
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms

/-!
# Principal coordinate opens for an admissible change

The transformed coordinates generate the same ideal as the original tuple.
Their principal opens therefore cover each normalized chart of the cubic.
-/

@[expose] public noncomputable section

open WeierstrassCurve AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassVariableChangeHomogeneous

variable {R : Type*} [CommRing R] (C : VariableChange R) (P : Fin 3 → R)

/-- Every transformed coordinate belongs to any ideal containing the original coordinates. -/
theorem coordinates_mem (I : Ideal R) (h : ∀ i, P i ∈ I) (j : Fin 3) :
    coordinates C P j ∈ I := by
  fin_cases j
  · exact I.add_mem (I.mul_mem_left _ (h 0)) (I.mul_mem_left _ (h 2))
  · exact I.add_mem (I.add_mem (I.mul_mem_left _ (h 1))
      (I.mul_mem_left _ (h 0))) (I.mul_mem_left _ (h 2))
  · exact h 2

/-- The homogeneous coordinate ideal is unchanged, even over rings with nilpotents. -/
theorem coordinates_span : Ideal.span (Set.range (coordinates C P)) =
    Ideal.span (Set.range P) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact coordinates_mem C P (Ideal.span (Set.range P))
      (fun j => Ideal.subset_span (Set.mem_range_self j)) i
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change P i ∈ Ideal.span (Set.range (coordinates C P))
    have h := coordinates_mem C⁻¹ (coordinates C P)
      (Ideal.span (Set.range (coordinates C P)))
      (fun j => Ideal.subset_span (Set.mem_range_self j)) i
    rw [coordinates_inv] at h
    exact h

/-- A normalized input has a transformed coordinate outside every prime ideal. -/
theorem exists_coordinate_notMem (j : Fin 3) (hj : P j = 1) (p : PrimeSpectrum R) :
    ∃ k, coordinates C P k ∉ p.asIdeal := by
  by_contra! h
  have he := coordinates_mem C⁻¹ (coordinates C P) p.asIdeal h j
  rw [coordinates_inv, hj] at he
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal he isUnit_one)

end FLT.Mazur.WeierstrassVariableChangeHomogeneous

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The transformed homogeneous coordinates on an original source chart. -/
def changedCoordinates (j : Fin 3) : Fin 3 → Coordinate (C • W) j :=
  WeierstrassVariableChangeHomogeneous.coordinates
    (C.map (algebraMap R (Coordinate (C • W) j))) (coord (C • W) j)

/-- Each chart is refined by the principal opens of all transformed coordinates. -/
def variableChangeCover : (integralCurve (C • W)).OpenCover where
  I₀ := Fin 3 × Fin 3
  X p := Spec (.of (Localization.Away (changedCoordinates W C p.1 p.2)))
  f p := PrincipalAffineRefinement.inclusion (changedCoordinates W C p.1 p.2) ≫
    integralCurveChart (C • W) p.1
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ => inferInstance⟩
    intro x
    obtain ⟨j, y, rfl⟩ := integralCurveChart_cover (C • W) x
    obtain ⟨k, hk⟩ := WeierstrassVariableChangeHomogeneous.exists_coordinate_notMem
      (C.map (algebraMap R (Coordinate (C • W) j))) (coord (C • W) j) j
      (coord_self (C • W) j) y
    have hy : y ∈ Set.range
        (PrincipalAffineRefinement.inclusion (changedCoordinates W C j k)) := by
      rw [PrincipalAffineRefinement.range_inclusion]
      exact hk
    obtain ⟨z, rfl⟩ := hy
    exact ⟨(j, k), z, rfl⟩

end FLT.Mazur.WeierstrassIntegralChart
