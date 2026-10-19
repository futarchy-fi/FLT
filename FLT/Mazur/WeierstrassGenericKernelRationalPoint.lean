/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedKernelClosure
public import FLT.Mazur.WeierstrassSmoothPointEquiv

/-!
# Original rational kernel points in the retained generic smooth cubic

A rational point of the original generic kernel determines a classical
projective point over exactly the original coefficient map. Its image in
every divided model is the retained generic point, with no coordinate choice.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K)))
  (r : Spec (.of K) ⟶ H)
  (hr : r ≫ i ≫ integralCurveStructure (W.map (algebraMap R K)) = 𝟙 _)

/-- The actual generic smooth factor preserves the original coefficient structure. -/
@[reassoc] theorem genericCurveToIntegralSmooth_structure :
    genericCurveToIntegralSmooth W hΔ ≫ integralSmoothStructure W =
      integralCurveStructure (W.map (algebraMap R K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [integralSmoothStructure, genericCurveToIntegralSmooth_inclusion_assoc]
  exact (integralCoefficient_isPullback W).w

/-- A rational point of the original kernel, as a point of the original integral smooth open. -/
def genericKernelRationalSmoothPoint : smoothCurveFieldPoint (K := K) W :=
  Over.homMk (r ≫ i ≫ genericCurveToIntegralSmooth W hΔ) (by
    change (r ≫ i ≫ genericCurveToIntegralSmooth W hΔ) ≫
      integralSmoothStructure W = Spec.map (CommRingCat.ofHom (algebraMap R K))
    rw [Category.assoc, Category.assoc, genericCurveToIntegralSmooth_structure]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) hr)

/-- Its classical point is recovered using the proved scheme/classical point equivalence. -/
def genericKernelProjectivePoint : (W.map (algebraMap R K)).toProjective.Point :=
  (smoothProjectivePointEquiv W).symm (genericKernelRationalSmoothPoint W hΔ i r hr)

/-- The recovered point retains the exact original generic kernel morphism. -/
@[reassoc] theorem genericKernelProjectivePoint_smooth :
    projectiveToSmooth W (genericKernelProjectivePoint W hΔ i r hr) =
      r ≫ i ≫ genericCurveToIntegralSmooth W hΔ :=
  congrArg Over.Hom.left ((smoothProjectivePointEquiv W).apply_symm_apply
    (genericKernelRationalSmoothPoint W hΔ i r hr))

end FLT.Mazur.WeierstrassIntegralChart
