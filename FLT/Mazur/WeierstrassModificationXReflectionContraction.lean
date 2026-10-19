/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInvolution
public import FLT.Mazur.WeierstrassModificationXMorphism
public import FLT.Mazur.WeierstrassGlobalNegation

/-!
# The original x-direction reflection contracts to Weierstrass negation

Identify the existing quadratic reflection with the genuine inverse on the
original cubic. The map retains the full incidence chart and coefficient base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "A" => Coordinate W s b3 b4 b6

/-- Reflection has the complete original vertical negation formula. -/
theorem initialReflection_y :
    initialReflection W s b3 b4 b6 (y W s b3 b4 b6) =
      -y W s b3 b4 b6 - algebraMap R A W.a₁ * x W s b3 b4 b6 -
        algebraMap R A (s * b3) := by
  have hc (z : R) : algebraMap R[X] A (C z) = algebraMap R A z :=
    (IsScalarTower.algebraMap_apply R R[X] A z).symm
  simp only [y, map_mul, initialReflection_x, initialReflection_v,
    polynomialSlopeLinear, map_add, hc]
  have he := incidence W s b3 b4 b6
  dsimp only [t] at he
  linear_combination -(algebraMap R A b3) * he

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- Reflection preserves the original affine contraction with its actual negative. -/
theorem initialReflection_fromOriginal :
    ((initialReflection W s b3 b4 b6).restrictScalars R).toAlgHom.comp
        (fromOriginal W s b3 b4 b6 h3 h4 h6) =
      (fromOriginal W s b3 b4 b6 h3 h4 h6).comp
        (WeierstrassIntegralChart.affineNegation W) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · simpa only [Fin.zero_eta, AlgHom.comp_apply, fromOriginal_x,
      WeierstrassIntegralChart.affineNegation_x, AlgEquiv.coe_toAlgHom,
      AlgEquiv.restrictScalars_apply] using
      initialReflection_x W s b3 b4 b6
  · simpa only [Fin.mk_one, AlgHom.comp_apply, fromOriginal_y,
      WeierstrassIntegralChart.affineNegation_y, map_sub, map_neg, map_mul,
      AlgHom.commutes, fromOriginal_x, h3, AlgEquiv.coe_toAlgHom,
      AlgEquiv.restrictScalars_apply] using
      initialReflection_y W s b3 b4 b6
  · simp [WeierstrassIntegralChart.coord_self]

/-- The original incidence chart has its actual integral reflection isomorphism. -/
def initialReflectionIso : Spec (.of A) ≅ Spec (.of A) :=
  Scheme.Spec.mapIso (initialReflection W s b3 b4 b6).toRingEquiv.toCommRingCatIso.op

/-- The scheme reflection is the original incidence algebra involution. -/
theorem initialReflectionIso_hom : (initialReflectionIso W s b3 b4 b6).hom =
    Spec.map (CommRingCat.ofHom (initialReflection W s b3 b4 b6).toRingHom) := rfl

/-- The whole incidence chart contracts equivariantly to the original global cubic. -/
@[reassoc] theorem initialReflectionIso_toCurve :
    (initialReflectionIso W s b3 b4 b6).hom ≫ toCurve W s b3 b4 b6 h3 h4 h6 =
      toCurve W s b3 b4 b6 h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveNegation W := by
  have hr : CommRingCat.ofHom (fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom ≫
      CommRingCat.ofHom (initialReflection W s b3 b4 b6).toRingHom =
      CommRingCat.ofHom (WeierstrassIntegralChart.affineNegation W).toRingHom ≫
        CommRingCat.ofHom (fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom :=
    congrArg (fun f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R]
      Coordinate W s b3 b4 b6 => CommRingCat.ofHom f.toRingHom)
      (initialReflection_fromOriginal W s b3 b4 b6 h3 h4 h6)
  unfold toCurve
  rw [initialReflectionIso_hom, Category.assoc,
    WeierstrassIntegralChart.integralCurveChart_negation_affine,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, hr, Spec.map_comp]

end FLT.Mazur.WeierstrassModificationX
