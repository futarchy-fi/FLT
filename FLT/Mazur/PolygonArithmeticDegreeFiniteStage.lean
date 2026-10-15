/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticIntegralDegree
public import FLT.Mazur.PolygonArithmeticStageProper
public import FLT.Mazur.ProperRingCohomologyFinite

/-!
# Finite homogeneous sections on the original polygon stages

Each actual stage is proper over the integral-base spectrum through its
closed coefficient immersion. Proper coherent cohomology gives finite
sections with exactly the original integral-base scalar action.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback SectionGradedSum Chow.AffineBase

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] (π : A)
  (n : ℕ) (h : 2 ≤ n) (m d : ℕ)

/-- Structural integral-base coefficients agree with the proper composite structure map. -/
theorem boundaryIntegralScalarMap_eq : boundaryIntegralScalarMap A π n h m =
    baseCohomologyScalars ((family A π m n h).hom ≫ baseToIntegral A π m) := by
  ext r
  change (family A π m n h).hom.appTop
    ((Scheme.ΓSpecIso (.of (Quotient A π m))).inv (Ideal.Quotient.mk (ideal A π ^ (m + 1)) r)) =
      ((family A π m n h).hom ≫ baseToIntegral A π m).appTop
        ((Scheme.ΓSpecIso (.of A)).inv r)
  rw [Scheme.Hom.comp_appTop]
  apply congrArg (family A π m n h).hom.appTop
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (ideal A π ^ (m + 1))))) r

/-- Insert actual zero-cohomology classes into their original homogeneous stage module. -/
def boundaryCohomologyToDegree :
    ModuleRingH (boundaryIntegralScalarMap A π n h m)
      (tensorPower (boundaryLine A π m n h) d) 0 →ₗ[A]
        boundaryIntegralDegree A π n h m d where
  toFun x := ⟨of (boundaryLine A π m n h) ⊤ d (moduleH0Equiv _ x), ⟨_, rfl⟩⟩
  map_add' x y := Subtype.ext (by simp only [map_add]; rfl)
  map_smul' r x := by
    apply Subtype.ext
    change of (boundaryLine A π m n h) ⊤ d
      (moduleH0Equiv _ (boundaryIntegralScalarMap A π n h m r •
        (show ModuleH (tensorPower (boundaryLine A π m n h) d) 0 from x))) = _
    rw [map_smul, map_smul, Algebra.smul_def, boundaryIntegralScalarMap_algebraMap]
    exact (boundaryIntegralDegree_smul_val A π n h m d r
      ⟨of (boundaryLine A π m n h) ⊤ d (moduleH0Equiv _ x), ⟨_, rfl⟩⟩).symm

/-- Homogeneous insertion reaches every original stage section in the specified degree. -/
theorem boundaryCohomologyToDegree_surjective :
    Function.Surjective (boundaryCohomologyToDegree A π n h m d) := by
  rintro ⟨s, ⟨u, rfl⟩⟩
  obtain ⟨x, hx⟩ := (moduleH0Equiv (tensorPower (boundaryLine A π m n h) d)).surjective u
  exact ⟨x, Subtype.ext (congrArg (of (boundaryLine A π m n h) ⊤ d) hx)⟩

variable [IsNoetherianRing A] [IsLocalRing A]
  (hgen : IsLocalRing.maximalIdeal A = ideal A π)

include hgen in
/-- Every original homogeneous stage module is finite over its actual integral coefficient base. -/
theorem boundaryIntegralDegree_finite : Module.Finite A
    (boundaryIntegralDegree A π n h m d) := by
  let _ := family_proper A π hgen m n h
  let _ := ((boundaryLine_rankOne A π m n h).tensorPower d).isFinitePresentation
  have hf := proper_coherent_hasFiniteRingCohomology
    ((family A π m n h).hom ≫ baseToIntegral A π m) (tensorPower (boundaryLine A π m n h) d) 0
  rw [← boundaryIntegralScalarMap_eq] at hf
  let _ := hf
  exact Module.Finite.of_surjective (boundaryCohomologyToDegree A π n h m d)
    (boundaryCohomologyToDegree_surjective A π n h m d)

end FLT.Mazur.PolygonArithmeticStages
