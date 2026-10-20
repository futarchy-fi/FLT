/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXNegation
public import FLT.Mazur.WeierstrassSuccessiveXContraction
public import FLT.Mazur.WeierstrassDilatationNegationContraction
public import FLT.Mazur.WeierstrassDilatationNegationDepth
public import FLT.Mazur.WeierstrassSuccessiveXSchemeOverlap

/-!
# The successive negative retains the actual divided contraction

The full incidence relation supplies the third-coefficient correction. The
result keeps the preceding divided equation and its original cubic morphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "N" => WeierstrassDilatation.negationIso W s (π * b3) (π * b4) (π ^ 2 * b6)

/-- The actual preceding algebra map commutes with the two constructed negatives. -/
theorem negation_fromDivided :
    (negation W s π b3 b4 b6).comp (fromDivided W s π b3 b4 b6) =
      (fromDivided W s π b3 b4 b6).comp
        (WeierstrassDilatation.negation W s (π * b3) (π * b4) (π ^ 2 * b6)) := by
  apply WeierstrassDilatation.hom_ext
  · simp only [AlgHom.comp_apply, fromDivided_x, negation_u,
      WeierstrassDilatation.negation_x]
  · simp only [AlgHom.comp_apply, fromDivided_y, map_mul, negation_u, negation_v,
      WeierstrassDilatation.negation_y, map_sub, map_neg, AlgHom.commutes, fromDivided_x]
    rw [← incidence W s π b3 b4 b6]
    ring

/-- The entire successive incidence scheme has its actual negation isomorphism. -/
def negationIso : Spec (.of A) ≅ Spec (.of A) :=
  Scheme.Spec.mapIso (negationEquiv W s π b3 b4 b6).toRingEquiv.toCommRingCatIso.op

/-- The constructed incidence negative retains the exact preceding divided morphism. -/
@[reassoc] theorem negationIso_toDivided :
    (negationIso W s π b3 b4 b6).hom ≫ toDivided W s π b3 b4 b6 =
      toDivided W s π b3 b4 b6 ≫ (N).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg Spec.map (congrArg (fun f : B →ₐ[R] A => CommRingCat.ofHom f.toRingHom)
    (negation_fromDivided W s π b3 b4 b6))

/-- The deeper divided negative contracts to the preceding negative by actual refinement. -/
@[reassoc] theorem dividedNegation_toPrevious :
    (WeierstrassDilatation.negationIso W (s * π) b3 b4 b6).hom ≫
        dividedToPrevious W s π b3 b4 b6 = dividedToPrevious W s π b3 b4 b6 ≫ (N).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg Spec.map (congrArg (fun f : B →ₐ[R]
    WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6 => CommRingCat.ofHom f.toRingHom)
    (WeierstrassDilatation.negation_refinement W s π
      (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl))

/-- The entire incidence chart retains the originally chosen projective cubic. -/
@[reassoc] theorem negationIso_toCurve
    (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
    (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6)) :
    (negationIso W s π b3 b4 b6).hom ≫ toCurve W s π b3 b4 b6 h3 h4 h6 =
      toCurve W s π b3 b4 b6 h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveNegation W := by
  rw [toCurve, negationIso_toDivided_assoc, WeierstrassDilatation.negationIso_toCurve]
  simp only [Category.assoc]

end FLT.Mazur.WeierstrassSuccessiveX
