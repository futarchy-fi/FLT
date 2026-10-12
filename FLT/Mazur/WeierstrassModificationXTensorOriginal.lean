/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXScaleOneTensor
public import FLT.Mazur.WeierstrassModificationXMorphism

/-!
# Original affine cubic functions on the actual coefficient tensor chart

The map is constructed from the original incidence contraction and the full
coefficient equivalence. It retains the original pure tensor coordinates.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (S : Type*) [CommRing S] [Algebra R S]
local notation "q" => algebraMap R S
local notation "V" => W.map q
local notation "T" => ScalarExtension W s b3 b4 b6 S
local notation "E" => baseChangeEquiv W s b3 b4 b6 S

/-- The original coefficient-extended affine contraction, before any root shear. -/
def tensorOriginalAffineMap : WeierstrassIntegralChart.Coordinate V 2 →ₐ[S] T :=
  (E).symm.toAlgHom.comp (fromOriginal V (q s) (q b3) (q b4) (q b6)
    (by simpa only [WeierstrassCurve.map_a₃, map_mul] using congrArg q h3)
    (by simpa only [WeierstrassCurve.map_a₄, map_mul] using congrArg q h4)
    (by simpa only [WeierstrassCurve.map_a₆, map_mul, map_pow] using congrArg q h6))

/-- The independent affine input preserves the complete original horizontal function. -/
theorem tensorOriginalAffineMap_x :
    tensorOriginalAffineMap W s b3 b4 b6 h3 h4 h6 S
      (WeierstrassIntegralChart.coord V 2 0) = (1 : S) ⊗ₜ[R] x W s b3 b4 b6 := by
  apply (E).injective
  simp only [tensorOriginalAffineMap, AlgHom.comp_apply, fromOriginal_x,
    AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply, baseChangeEquiv_tmul, one_smul]
  exact (coefficientMap_x W s b3 b4 b6 S).symm

/-- The independent affine input preserves the complete original vertical function. -/
theorem tensorOriginalAffineMap_y :
    tensorOriginalAffineMap W s b3 b4 b6 h3 h4 h6 S
      (WeierstrassIntegralChart.coord V 2 1) = (1 : S) ⊗ₜ[R] y W s b3 b4 b6 := by
  apply (E).injective
  simp only [tensorOriginalAffineMap, AlgHom.comp_apply, fromOriginal_y,
    AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply, baseChangeEquiv_tmul, one_smul]
  rw [y, y, map_mul, coefficientMap_x, coefficientMap_v]

end FLT.Mazur.WeierstrassModificationX
