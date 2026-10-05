/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCanonicalOverlapChart
public import FLT.Mazur.AffineCanonicalOverlapRecognition
public import FLT.Mazur.AffineGeometricRefinementData
public import FLT.Mazur.SchemeCanonicalOverlapRefinement

/-!
# Coaction compatibility survives affine refinement

The actual refined geometric datum is compatible with the restricted
reconstruction chart. The proof passes through canonical geometric overlaps,
using the actual categorical fiber-product and tensor-spectrum charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineRefinementPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ)

/-- The affine square comparison is the general scheme square comparison. -/
theorem squareIso_eq_scheme : squareIso φ ψ a b w =
    SchemePullbackSquare.squareIso (Spec.map φ) (Spec.map ψ) (Spec.map a) (Spec.map b)
      (spec_square φ ψ a b w) := by
  apply Iso.ext
  simp only [squareIso, SchemePullbackSquare.squareIso,
    SheafPullbackPathComparison.comparison, Iso.trans_hom, Category.assoc]

/-- The affine reconstruction has exactly the general square's chart. -/
theorem reconstruction_eq_scheme {A : (Spec R).Modules} {M : (Spec S).Modules}
    (e : (pullback (Spec.map φ)).obj A ≅ M) :
    reconstruction φ ψ a b w e =
      (SchemePullbackSquare.squareIso (Spec.map φ) (Spec.map ψ) (Spec.map a) (Spec.map b)
        (spec_square φ ψ a b w)).app A ≪≫ (pullback (Spec.map b)).mapIso e := by
  rw [reconstruction, squareIso_eq_scheme]

end FLT.Mazur.AffineRefinementPullback

namespace FLT.Mazur.AffineGeometricDescentRecognition
open AffineGeometricDescent AffineGeometricOverlap SchemePullbackOverlap
attribute [local irreducible] SchemePullbackOverlap.chartOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ)
variable (A : (Spec R).Modules) [A.IsQuasicoherent]
variable {M : (Spec S).Modules} [M.IsQuasicoherent] (D : Data φ M)
variable (e : (pullback (Spec.map φ)).obj A ≅ M)
local instance : ((pullback (Spec.map a)).obj A).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback a A
local instance : ((pullback (Spec.map b)).obj M).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback b M

/-- The actual refined datum is compatible with the transported reconstruction. -/
theorem refinement_compatible (he : CoactionCompatible φ A D e) :
    CoactionCompatible ψ ((pullback (Spec.map a)).obj A)
      (AffineGeometricOverlapRefinement.data φ ψ a b w M D)
      (AffineRefinementPullback.reconstruction φ ψ a b w e) := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  have hd := (coactionCompatible_iff_canonical_overlap φ A D e
    (canonicalTensorBase R S) (canonicalTensorBase_left R S)
    (canonicalTensorBase_right R S)).mp he
  apply (coactionCompatible_iff_canonical_overlap ψ ((pullback (Spec.map a)).obj A)
    (AffineGeometricOverlapRefinement.data φ ψ a b w M D)
    (AffineRefinementPullback.reconstruction φ ψ a b w e)
    (canonicalTensorBase R' S') (canonicalTensorBase_left R' S')
    (canonicalTensorBase_right R' S')).mpr
  change fromFiberProduct R' S' ((pullback (Spec.map b)).obj M)
    (SchemeOverlapRefinement.refine (Spec.map φ) (Spec.map ψ) (Spec.map a) (Spec.map b)
      (AffineRefinementPullback.spec_square φ ψ a b w) (toFiberProduct R S M D.val)) = _
  rw [hd]
  erw [toFiberProduct_chartOverlap R S A e]
  erw [SchemeOverlapRefinement.refine_chartOverlap (Spec.map φ) (Spec.map ψ)
    (Spec.map a) (Spec.map b) (AffineRefinementPullback.spec_square φ ψ a b w)
    (canonicalFiberBase R S) rfl Limits.pullback.condition.symm
    (canonicalFiberBase R' S') rfl Limits.pullback.condition.symm A e]
  rw [AffineRefinementPullback.reconstruction_eq_scheme]
  exact fromFiberProduct_chartOverlap R' S' ((pullback (Spec.map a)).obj A)
    ((SchemePullbackSquare.squareIso (Spec.map φ) (Spec.map ψ) (Spec.map a) (Spec.map b)
      (AffineRefinementPullback.spec_square φ ψ a b w)).app A ≪≫
      (pullback (Spec.map b)).mapIso e)

end FLT.Mazur.AffineGeometricDescentRecognition
