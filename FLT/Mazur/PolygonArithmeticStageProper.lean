/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticResidueNilpotence
public import FLT.Mazur.PolygonInfinitesimalStageProper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Proper arithmetic polygon thickenings

The original residue polygon is proper and covers the entire underlying
arithmetic stage. Universal closedness descends through its inclusion;
separatedness and finite presentation then give properness. In a discrete
valuation ring the sole parameter condition follows from irreducibility.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.PolygonArithmeticStages
universe u
variable (A : Type u) [CommRing A] [IsLocalRing A] (π : A)
  (hgen : maximalIdeal A = ideal A π) (m n : ℕ) (h : 2 ≤ n)

include hgen in
/-- The entire arithmetic family is universally closed over its original quotient base. -/
theorem family_universallyClosed : UniversallyClosed (family A π m n h).hom := by
  let hπ := parameter_residue_zero A π hgen
  let _ := residueFiberInclusion_surjective A π hgen hπ m n h
  let _ := PolygonInfinitesimalStages.cyclicPolygon_proper (ResidueField A) n h
  have hc : UniversallyClosed
      (residueFiberInclusion A π hπ m n h ≫ (family A π m n h).hom) := by
    rw [(residueFiberInclusion_isPullback A π hπ m n h).w]
    infer_instance
  exact UniversallyClosed.of_comp_surjective (residueFiberInclusion A π hπ m n h) _

include hgen in
/-- All finite arithmetic polygon stages are proper, also in mixed characteristic. -/
theorem family_proper : IsProper (family A π m n h).hom := by
  let _ := family_universallyClosed A π hgen m n h
  exact ⟨⟩

variable [IsDomain A] [IsDiscreteValuationRing A]

omit [IsLocalRing A] in
/-- An actual uniformizer supplies properness without a residue coefficient-field lift. -/
theorem family_proper_of_irreducible (hπ : Irreducible π) :
    IsProper (family A π m n h).hom :=
  family_proper A π ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ) m n h

end FLT.Mazur.PolygonArithmeticStages
