/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveAffineChartEmbedding
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Properness of polynomial projective space

The degree-zero homogeneous coordinate ring consists exactly of constants.
Its explicit equivalence with the coefficient ring identifies the existing
base projection with the proper projection of Proj followed by an isomorphism.
Finite coordinates generate the polynomial ring over its degree-zero part.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u v

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type v)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A degree-zero homogeneous polynomial is its constant coefficient. -/
lemma degreeZero_eq_constant (p : grading R ι 0) :
    (p : MvPolynomial ι R) = C (constantCoeff (p : MvPolynomial ι R)) := by
  exact totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous ι).mpr p.property)

/-- The coefficient ring is explicitly the degree-zero homogeneous ring. -/
def constantsEquivZero : R ≃+* grading R ι 0 :=
  { constantsToZero R ι with
    invFun := fun p ↦ constantCoeff (p : MvPolynomial ι R)
    left_inv := fun r ↦ by simp [constantsToZero]
    right_inv := fun p ↦ Subtype.ext (degreeZero_eq_constant R ι p).symm }

/-- The equivalence uses the same constants map as the existing projection. -/
@[simp]
lemma constantsEquivZero_toRingHom :
    (constantsEquivZero R ι : R →+* grading R ι 0) = constantsToZero R ι := rfl

@[simp]
lemma constantsEquivZero_symm_apply (p : grading R ι 0) :
    (constantsEquivZero R ι).symm p = constantCoeff (p : MvPolynomial ι R) := rfl

/-- Finitely many coordinates generate over the degree-zero ring. -/
instance finiteTypeOverZero [Finite ι] :
    Algebra.FiniteType (grading R ι 0) (MvPolynomial ι R) := by
  classical
  let := Fintype.ofFinite ι
  refine ⟨⟨Finset.univ.image X, ?_⟩⟩
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
    adjoin_coordinates R ι

/-- Constants induce the spectrum isomorphism used in the base projection. -/
def constantsSpecIso (R : Type (max u v)) [CommRing R] (ι : Type v) :
    Spec (.of (grading R ι 0)) ≅ Spec (.of R) :=
  Scheme.Spec.mapIso (constantsEquivZero R ι).toCommRingCatIso.op

@[simp]
lemma constantsSpecIso_hom (R : Type (max u v)) [CommRing R] (ι : Type v) :
    (constantsSpecIso R ι).hom = Spec.map (CommRingCat.ofHom (constantsToZero R ι)) := rfl

/-- The existing projective-space projection is proper for finite coordinates. -/
instance baseProjection_isProper (R : Type (max u v)) [CommRing R]
    (ι : Type v) [Finite ι] : IsProper (baseProjection R ι) := by
  rw [baseProjection, ← constantsSpecIso_hom]
  infer_instance

end FLT.Mazur.ProjectiveSpace
