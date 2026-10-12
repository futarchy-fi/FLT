/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXShear
public import FLT.Mazur.WeierstrassDilatationShear
public import FLT.Mazur.WeierstrassSuccessiveXContraction

/-!
# The successive shear retains the preceding divided contraction

Correct the fourth preceding quotient by its forced distributive identity.
The resulting actual algebra equivalence commutes with (u,v) ↦ (u,uv).
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r
local notation "A" => WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "B" => WeierstrassDilatation.Coordinate U s
  (π * b3) (π * (b4 - r * b3)) (π ^ 2 * b6)

/-- The actual preceding divided shear, with the forced fourth quotient retained. -/
def precedingShearEquiv : A ≃ₐ[R] B :=
  (WeierstrassDilatation.shearEquiv W s (π * b3) (π * b4) (π ^ 2 * b6) r).trans
    (WeierstrassDilatation.parameterEquiv U s s (π * b3) (π * b4 - r * (π * b3))
      (π ^ 2 * b6) (π * b3) (π * (b4 - r * b3)) (π ^ 2 * b6)
      rfl rfl (by ring) rfl)

/-- The preceding horizontal coordinate is unchanged. -/
theorem precedingShearEquiv_x :
    precedingShearEquiv W s π b3 b4 b6 r
        (WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)) =
      WeierstrassDilatation.x U s (π * b3) (π * (b4 - r * b3)) (π ^ 2 * b6) := by
  rw [precedingShearEquiv, AlgEquiv.trans_apply]
  have he : ⇑(WeierstrassDilatation.shearEquiv W s (π * b3) (π * b4) (π ^ 2 * b6) r) =
      ⇑(WeierstrassDilatation.shearForward W s (π * b3) (π * b4) (π ^ 2 * b6) r) := rfl
  rw [he]
  rw [WeierstrassDilatation.shearForward_x, WeierstrassDilatation.parameterEquiv_x]

/-- The preceding vertical coordinate retains the full linear shear. -/
theorem precedingShearEquiv_y :
    precedingShearEquiv W s π b3 b4 b6 r
        (WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)) =
      WeierstrassDilatation.y U s (π * b3) (π * (b4 - r * b3)) (π ^ 2 * b6) +
        algebraMap R B r *
          WeierstrassDilatation.x U s (π * b3) (π * (b4 - r * b3)) (π ^ 2 * b6) := by
  rw [precedingShearEquiv, AlgEquiv.trans_apply]
  have he : ⇑(WeierstrassDilatation.shearEquiv W s (π * b3) (π * b4) (π ^ 2 * b6) r) =
      ⇑(WeierstrassDilatation.shearForward W s (π * b3) (π * b4) (π ^ 2 * b6) r) := rfl
  rw [he]
  rw [WeierstrassDilatation.shearForward_y, map_add, map_mul, AlgEquiv.commutes,
    WeierstrassDilatation.parameterEquiv_x, WeierstrassDilatation.parameterEquiv_y]

/-- The whole successive incidence contraction commutes with the actual preceding shear. -/
theorem shearForward_fromDivided :
    (shearForward W s π b3 b4 b6 r).comp (fromDivided W s π b3 b4 b6) =
      (fromDivided U s π b3 (b4 - r * b3) b6).comp
        (precedingShearEquiv W s π b3 b4 b6 r).toAlgHom := by
  apply WeierstrassDilatation.hom_ext
  · simp [precedingShearEquiv_x]
  · simp [precedingShearEquiv_y, mul_add, mul_comm]

/-- The affine scheme comparison retains the full original successive contraction. -/
@[reassoc] theorem shearSpec_toDivided :
    Spec.map (CommRingCat.ofHom (shearForward W s π b3 b4 b6 r).toRingHom) ≫
        toDivided W s π b3 b4 b6 =
      toDivided U s π b3 (b4 - r * b3) b6 ≫
        Spec.map (CommRingCat.ofHom (precedingShearEquiv W s π b3 b4 b6 r).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (shearForward_fromDivided W s π b3 b4 b6 r)

end FLT.Mazur.WeierstrassSuccessiveX
