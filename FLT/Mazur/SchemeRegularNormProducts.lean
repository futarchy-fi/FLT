/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeNormIndependentGroundTests

/-!
# Products of regular norm neighborhoods

The global regular norm is multiplicative and independent of the chosen
finite translation basis. Products therefore refine norm neighborhoods by
intersection, without requiring a global affine source or extending sections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
universe u v w
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeEffectiveEpiSections AffineProductTranslationNorm
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] (Y V : Over (Spec (.of R))) [IsAffine V.left]
/-- Norm products use the original translation section algebra. -/
local instance productsTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type v} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))

/-- Affine tests detect equality of regular functions on an arbitrary source. -/
theorem section_eq_of_affineTests (s t : Γ(Y.left, ⊤))
    (h : ∀ i, (Y.left.affineCover.f i).appTop s =
      (Y.left.affineCover.f i).appTop t) : s = t := by
  apply (functionEquiv Y.left).symm.injective
  apply Y.left.affineCover.hom_ext
  intro i
  apply (functionEquiv (Y.left.affineCover.X i)).injective
  simpa only [functionEquiv_comp, Equiv.apply_symm_apply] using h i

/-- The global determinant norm preserves the unit function. -/
theorem regularNorm_one : regularNorm Y V b 1 = 1 := by
  apply section_eq_of_affineTests Y
  intro i
  rw [regularNorm_independentTest, map_one, envelopeNorm_eq_section_norm, map_one, map_one]

/-- Products of envelope sections give products of their actual global regular norms. -/
theorem regularNorm_mul (s t : Γ((prod Y V).left, ⊤)) :
    regularNorm Y V b (s * t) = regularNorm Y V b s * regularNorm Y V b t := by
  apply section_eq_of_affineTests Y
  intro i
  rw [map_mul, regularNorm_independentTest, regularNorm_independentTest,
    regularNorm_independentTest, map_mul, envelopeNorm_eq_section_norm,
    envelopeNorm_eq_section_norm, envelopeNorm_eq_section_norm, map_mul]

/-- The actual regular norm is a multiplicative map on all envelope sections. -/
def regularNormMonoidHom : Γ((prod Y V).left, ⊤) →* Γ(Y.left, ⊤) where
  toFun := regularNorm Y V b
  map_one' := regularNorm_one Y V b
  map_mul' := regularNorm_mul Y V b

/-- Taking powers is compatible with the actual regular norm. -/
theorem regularNorm_pow (s : Γ((prod Y V).left, ⊤)) (n : ℕ) :
    regularNorm Y V b (s ^ n) = regularNorm Y V b s ^ n :=
  (regularNormMonoidHom Y V b).map_pow s n

/-- Different finite bases give literally the same global coefficient. -/
theorem regularNorm_basis_independent {κ : Type w} [Finite κ]
    (c : Basis κ R Γ(V.left, ⊤)) (s : Γ((prod Y V).left, ⊤)) :
    regularNorm Y V b s = regularNorm Y V c s := by
  apply section_eq_of_affineTests Y
  intro i
  rw [regularNorm_independentTest, regularNorm_independentTest,
    envelopeNorm_eq_section_norm, envelopeNorm_eq_section_norm]

/-- Multiplying norm coefficients constructs the intersection of their actual neighborhoods. -/
theorem basicOpen_regularNorm_mul (s t : Γ((prod Y V).left, ⊤)) :
    Y.left.basicOpen (regularNorm Y V b (s * t)) =
      Y.left.basicOpen (regularNorm Y V b s) ⊓ Y.left.basicOpen (regularNorm Y V b t) := by
  rw [regularNorm_mul, Scheme.basicOpen_mul]

end FLT.Mazur.SchemeTranslationNorm
