/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYAlgebra
public import FLT.Mazur.PrincipalAffineRefinement
public import Mathlib.RingTheory.Coprime.Basic

/-!
# The two principal opens cover the y-direction chart

The divided cubic supplies explicit Bezout coefficients for r=s/y and u=x/y.
Consequently their actual localization spectra cover the entire equation chart.
No smoothness, flatness, or residue-field assumption is needed for this cover.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationY

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The scale and horizontal ratios generate the unit ideal in the actual chart. -/
theorem ratios_coprime : IsCoprime (coord W s b3 b4 b6 0) (coord W s b3 b4 b6 1) := by
  refine ⟨algebraMap R _ b4 * coord W s b3 b4 b6 1 +
      algebraMap R _ b6 * coord W s b3 b4 b6 0 - algebraMap R _ b3,
    coord W s b3 b4 b6 2 * coord W s b3 b4 b6 1 ^ 2 +
      algebraMap R _ W.a₂ * coord W s b3 b4 b6 1 - algebraMap R _ W.a₁, ?_⟩
  linear_combination -(equation W s b3 b4 b6)

/-- Every prime of the y-chart avoids at least one of the two ratios. -/
theorem ratio_exists_not_mem (p : PrimeSpectrum (Coordinate W s b3 b4 b6)) :
    ∃ i : Fin 2, coord W s b3 b4 b6 i.castSucc ∉ p.asIdeal := by
  by_contra h
  push Not at h
  obtain ⟨a, b, hab⟩ := ratios_coprime W s b3 b4 b6
  have h0 := p.asIdeal.mul_mem_left a (h 0)
  have h1 := p.asIdeal.mul_mem_left b (h 1)
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal (by
    simpa only [Fin.castSucc_zero, Fin.castSucc_one, hab] using p.asIdeal.add_mem h0 h1)
    isUnit_one)

/-- The corresponding basic opens cover the actual prime spectrum. -/
theorem ratio_basicOpen_cover :
    (⨆ i : Fin 2, PrimeSpectrum.basicOpen (coord W s b3 b4 b6 i.castSucc)) = ⊤ := by
  apply TopologicalSpace.Opens.ext
  ext p
  simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion,
    TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  exact ratio_exists_not_mem W s b3 b4 b6 p

/-- The y-direction chart is covered by its actual two ratio localizations. -/
def ratioCover : (Spec (.of (Coordinate W s b3 b4 b6))).OpenCover where
  I₀ := Fin 2
  X i := Spec (.of (Localization.Away (coord W s b3 b4 b6 i.castSucc)))
  f i := PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 i.castSucc)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ => inferInstance⟩
    intro p
    obtain ⟨i, hi⟩ := ratio_exists_not_mem W s b3 b4 b6 p
    refine ⟨i, ?_⟩
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hi

end FLT.Mazur.WeierstrassModificationY
