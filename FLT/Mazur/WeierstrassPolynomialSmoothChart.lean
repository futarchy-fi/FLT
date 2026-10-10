/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassPolynomialFieldSmooth
public import FLT.Mazur.WeierstrassProjectiveSmoothResidues

/-!
# The polynomial addition charts restricted to actual smooth inputs

For every pair of input charts and every output normalization, the original
polynomial addition morphism sends its full smooth-input open into the relative
smooth locus. No discriminant or reducedness hypothesis is needed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (j k t : Fin 3)

/-- The original left input of a normalized polynomial addition chart. -/
def polynomialInputLeft : Coordinate W j →ₐ[R] AdditionOutputOpen W j k t :=
  (additionOutputRestriction W j k t).comp (chartProductLeft W j k)

/-- The original right input of a normalized polynomial addition chart. -/
def polynomialInputRight : Coordinate W k →ₐ[R] AdditionOutputOpen W j k t :=
  (additionOutputRestriction W j k t).comp (chartProductRight W j k)

/-- The actual smooth-input open in the original polynomial output domain. -/
def polynomialSmoothInputOpen : (Spec (.of (AdditionOutputOpen W j k t))).Opens :=
  (Spec.map (CommRingCat.ofHom (polynomialInputLeft W j k t).toRingHom) ≫
      integralCurveChart W j) ⁻¹ᵁ integralSmoothOpen W ⊓
    (Spec.map (CommRingCat.ofHom (polynomialInputRight W j k t).toRingHom) ≫
      integralCurveChart W k) ⁻¹ᵁ integralSmoothOpen W

/-- Every polynomial chart sends all actual smooth inputs into the relative smooth locus. -/
theorem polynomialSmoothInputOpen_output (p : Spec (.of (AdditionOutputOpen W j k t)))
    (hp : p ∈ polynomialSmoothInputOpen W j k t) :
    (Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) ≫
      integralCurveChart W t) p ∈ integralSmoothOpen W := by
  apply chartAlgebra_smooth_at_of_residue W t (projectiveAdditionChart W j k t) p
  exact polynomialFieldPoint_nonsingular W j k t (IsScalarTower.toAlgHom R _ _)
    (chartAlgebra_residue_nonsingular_at W j (polynomialInputLeft W j k t) p hp.1)
    (chartAlgebra_residue_nonsingular_at W k (polynomialInputRight W j k t) p hp.2)

/-- The original polynomial addition morphism restricted to its full smooth-input open. -/
def polynomialSmoothChart :
    (polynomialSmoothInputOpen W j k t).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι
    ((polynomialSmoothInputOpen W j k t).ι ≫
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) ≫
        integralCurveChart W t) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact polynomialSmoothInputOpen_output W j k t p.val p.property)

/-- Restricting the polynomial output retains the entire original scheme morphism. -/
@[reassoc] theorem polynomialSmoothChart_inclusion :
    polynomialSmoothChart W j k t ≫ (integralSmoothOpen W).ι =
      (polynomialSmoothInputOpen W j k t).ι ≫
        Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) ≫
          integralCurveChart W t :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restricted polynomial addition is over the original coefficient spectrum. -/
theorem polynomialSmoothChart_structure :
    polynomialSmoothChart W j k t ≫ integralSmoothStructure W =
      (polynomialSmoothInputOpen W j k t).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AdditionOutputOpen W j k t))) := by
  rw [integralSmoothStructure, polynomialSmoothChart_inclusion_assoc,
    integralCurveChart_structure]
  rw [chartStructure, specAlgHom_structure (projectiveAdditionChart W j k t)]

end FLT.Mazur.WeierstrassIntegralChart
