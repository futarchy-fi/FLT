/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineRelativeSmoothCriterion
public import FLT.Mazur.WeierstrassDilatationReesChart

/-!
# The modification center misses the original relative smooth locus

At every prime containing (s,x,y), both affine derivatives vanish in the
residue field. Thus every relatively smooth point lies in a principal open
of an actual center generator, without any discriminant hypothesis.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4)

include h3 h4

/-- A smooth affine point avoids at least one generator of the actual center. -/
theorem smooth_avoids_modification_generators (p : PrimeSpectrum (Coordinate W 2))
    (hp : p ∈ (chartStructure W 2).smoothLocus) :
    algebraMap R (Coordinate W 2) s ∉ p.asIdeal ∨
      coord W 2 0 ∉ p.asIdeal ∨ coord W 2 1 ∉ p.asIdeal := by
  by_contra! h
  obtain ⟨hs, hx, hy⟩ := h
  have hn := affineRelativeSmooth_nonsingular W p hp
  have hx' := Ideal.algebraMap_residueField_eq_zero.mpr hx
  have hy' := Ideal.algebraMap_residueField_eq_zero.mpr hy
  have hs' : algebraMap R p.asIdeal.ResidueField s = 0 := by
    rw [IsScalarTower.algebraMap_apply R (Coordinate W 2) p.asIdeal.ResidueField]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hs
  rw [hx', hy', WeierstrassCurve.Affine.nonsingular_zero] at hn
  simpa [WeierstrassCurve.map, h3, h4, map_mul, hs'] using hn.2

/-- The actual center's vanishing set is disjoint from the original smooth open. -/
theorem modificationCenter_not_le_of_smooth (p : PrimeSpectrum (Coordinate W 2))
    (hp : p ∈ (chartStructure W 2).smoothLocus) :
    ¬ WeierstrassDilatation.modificationCenter W s ≤ p.asIdeal := by
  intro h
  have hm (f : Coordinate W 2)
      (hf : f ∈ ({algebraMap R (Coordinate W 2) s, coord W 2 0, coord W 2 1} : Set _)) :
      f ∈ p.asIdeal := h (Ideal.subset_span hf)
  rcases smooth_avoids_modification_generators W s b3 b4 h3 h4 p hp with hs | hx | hy
  · exact hs (hm _ (by simp))
  · exact hx (hm _ (by simp))
  · exact hy (hm _ (by simp))

end FLT.Mazur.WeierstrassIntegralChart
