/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationNegation
public import FLT.Mazur.WeierstrassDilatationMorphism
public import FLT.Mazur.WeierstrassGlobalNegation

/-!
# Divided negation retains the original cubic

The integral chart involution contracts to the original global Weierstrass
negative. Both the original coefficient map and every original equation remain.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- Divided negation is precisely the original affine negation after contraction. -/
theorem negation_fromOriginal :
    (negation W s b3 b4 b6).comp (fromOriginal W s b3 b4 b6 h3 h4 h6) =
      (fromOriginal W s b3 b4 b6 h3 h4 h6).comp
        (WeierstrassIntegralChart.affineNegation W) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, AlgHom.comp_apply, fromOriginal_x,
      WeierstrassIntegralChart.affineNegation_x, map_mul, AlgHom.commutes, negation_x]
  · simp only [Fin.mk_one, AlgHom.comp_apply, fromOriginal_y,
      WeierstrassIntegralChart.affineNegation_y, map_sub, map_neg, map_mul,
      AlgHom.commutes, fromOriginal_x, negation_y, h3]
    ring
  · simp [WeierstrassIntegralChart.coord_self]

/-- The actual affine divided scheme has a negation automorphism over the full base. -/
def negationIso : Spec (.of (Coordinate W s b3 b4 b6)) ≅
    Spec (.of (Coordinate W s b3 b4 b6)) :=
  Scheme.Spec.mapIso (negationEquiv W s b3 b4 b6).toRingEquiv.toCommRingCatIso.op

/-- The underlying scheme map is the actual divided algebra negative. -/
theorem negationIso_hom : (negationIso W s b3 b4 b6).hom =
    Spec.map (CommRingCat.ofHom (negation W s b3 b4 b6).toRingHom) := rfl

/-- The scheme automorphism retains the specified original projective contraction. -/
@[reassoc] theorem negationIso_toCurve :
    (negationIso W s b3 b4 b6).hom ≫ toCurve W s b3 b4 b6 h3 h4 h6 =
      toCurve W s b3 b4 b6 h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveNegation W := by
  have hr : CommRingCat.ofHom (fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom ≫
      CommRingCat.ofHom (negation W s b3 b4 b6).toRingHom =
      CommRingCat.ofHom (WeierstrassIntegralChart.affineNegation W).toRingHom ≫
        CommRingCat.ofHom (fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom :=
    congrArg (fun f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R]
      Coordinate W s b3 b4 b6 => CommRingCat.ofHom f.toRingHom)
      (negation_fromOriginal W s b3 b4 b6 h3 h4 h6)
  unfold toCurve
  rw [negationIso_hom, Category.assoc,
    WeierstrassIntegralChart.integralCurveChart_negation_affine,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, hr, Spec.map_comp]

/-- Negation fixes the exact integral coefficient morphism. -/
@[reassoc] theorem negationIso_structure :
    (negationIso W s b3 b4 b6).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s b3 b4 b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s b3 b4 b6))) :=
  WeierstrassIntegralChart.specAlgHom_structure (negation W s b3 b4 b6)

end FLT.Mazur.WeierstrassDilatation
