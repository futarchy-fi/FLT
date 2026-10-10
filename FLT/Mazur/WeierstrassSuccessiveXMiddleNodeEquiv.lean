/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeMaps
public import FLT.Mazur.WeierstrassModificationXConicFirstInverse

/-!
# The whole first middle attachment is an actual node neighborhood

The original open at v+a₁ is isomorphic to the standard node z*u=0 localized
at 1-c*z². Both inverse identities retain every original generator.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "O" => MiddleFirstOpen W c
local notation "N" => MiddleNodeOpen c
local notation "B" => SuccessiveIncidence.Coordinate (0 : R)
local notation "f" => middleNodeToFirst W c h2 ha
local notation "g" => middleFirstToNode W c h2 ha

/-- The full-node map retains the existing conic parameter map. -/
theorem middleNodeToFirst_parameterMap :
    (f).comp (conicParameterToMiddleNode c) =
      (conicFirstToMiddleFirst W c h2).comp (conicParameterToFirst W.a₁ c ha) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (conicParameterPolynomial c))
  apply Polynomial.algHom_ext
  change f (conicParameterToMiddleNode c (conicParameterZ c)) =
    conicFirstToMiddleFirst W c h2 (conicParameterToFirst W.a₁ c ha (conicParameterZ c))
  rw [conicParameterToMiddleNode_z, middleNodeToFirst_z, conicParameterToFirst_z,
    conicFirstToMiddleFirst_parameter]

/-- The inverse incidence formula recovers the original t on the whole neighborhood. -/
@[simp] theorem middleNodeToFirst_t :
    f (middleNodeT W.a₁ c) = algebraMap A O (coord W 0 0 0 0 c 0) := by
  have h := DFunLike.congr_fun (middleNodeToFirst_parameterMap W c h2 ha)
    (conicInverseT W.a₁ c)
  change f (middleNodeT W.a₁ c) = _ at h
  rw [AlgHom.comp_apply, conicParameterToFirst_inverseT,
    conicFirstToMiddleFirst_base, middleConicSection_t] at h
  exact h

/-- The inverse slope formula recovers the original v on the whole neighborhood. -/
@[simp] theorem middleNodeToFirst_v :
    f (middleNodeV W.a₁ c) = algebraMap A O (coord W 0 0 0 0 c 1) := by
  have h := DFunLike.congr_fun (middleNodeToFirst_parameterMap W c h2 ha)
    (conicInverseV W.a₁ c)
  change f (middleNodeV W.a₁ c) = _ at h
  rw [AlgHom.comp_apply, conicParameterToFirst_inverseV,
    conicFirstToMiddleFirst_base, middleConicSection_v] at h
  exact h

/-- The actual full first middle attachment is precisely a principal open of a node. -/
def middleFirstNodeEquiv : O ≃ₐ[R] N := by
  apply AlgEquiv.ofAlgHom g f
  · apply IsLocalization.algHom_ext (Submonoid.powers (middleNodeDenominator c))
    apply SuccessiveIncidence.hom_ext
    · change g (f (middleNodeZ c)) = middleNodeZ c
      rw [middleNodeToFirst_z, middleFirstToNode_parameter]
    · change g (f (middleNodeU c)) = middleNodeU c
      rw [middleNodeToFirst_u, middleFirstToNode_base, middleFirstToNodeBase_coord]
      rfl
  · apply IsLocalization.algHom_ext
      (Submonoid.powers (coord W 0 0 0 0 c 1 + algebraMap R A W.a₁))
    apply hom_ext
    intro i
    change f (g (algebraMap A O (coord W 0 0 0 0 c i))) = _
    rw [middleFirstToNode_base, middleFirstToNodeBase_coord]
    fin_cases i
    · exact middleNodeToFirst_t W c h2 ha
    · exact middleNodeToFirst_v W c h2 ha
    · exact middleNodeToFirst_u W c h2 ha

/-- The actual coordinate comparison preserves the original horizontal branch function. -/
theorem middleFirstNodeEquiv_u :
    middleFirstNodeEquiv W c h2 ha (algebraMap A O (coord W 0 0 0 0 c 2)) =
      middleNodeU c := by
  change g (algebraMap A O (coord W 0 0 0 0 c 2)) = _
  rw [middleFirstToNode_base, middleFirstToNodeBase_coord]
  rfl

/-- The actual coordinate comparison preserves the original rational incidence parameter. -/
theorem middleFirstNodeEquiv_parameter :
    middleFirstNodeEquiv W c h2 ha (middleFirstParameter W c) = middleNodeZ c :=
  middleFirstToNode_parameter W c h2 ha

end FLT.Mazur.WeierstrassSuccessiveX
