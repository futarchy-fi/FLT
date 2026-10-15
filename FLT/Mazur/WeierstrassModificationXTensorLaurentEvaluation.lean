/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentEvaluation
public import FLT.Mazur.WeierstrassModificationXBaseChangeGenerators

/-!
# Initial Laurent evaluation on the full original tensor chart

The original tensor generators determine every map. The independently
constructed initial Laurent root evaluates all functions after base change.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]
local notation "A" => Coordinate W s b3 b4 b6
local notation "T₀" => S ⊗[R] A

/-- The two original tensor coordinates determine every map over the extended coefficients. -/
theorem tensorEvaluation_ext {B : Type*} [CommRing B] [Algebra S B]
    [Algebra R B] [IsScalarTower R S B] (f g : T₀ →ₐ[S] B)
    (ht : f ((1 : S) ⊗ₜ[R] t W s b3 b4 b6) = g ((1 : S) ⊗ₜ[R] t W s b3 b4 b6))
    (hv : f ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) = g ((1 : S) ⊗ₜ[R] v W s b3 b4 b6)) :
    f = g := by
  have he : (f.restrictScalars R).comp Algebra.TensorProduct.includeRight =
      (g.restrictScalars R).comp Algebra.TensorProduct.includeRight :=
    hom_ext W s b3 b4 b6 _ _ ht hv
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    have hz := AlgHom.congr_fun he z
    change f ((1 : S) ⊗ₜ[R] z) = g ((1 : S) ⊗ₜ[R] z) at hz
    rw [show a ⊗ₜ[R] z = a • ((1 : S) ⊗ₜ[R] z) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul, hz]
  | add z w hz hw => simp only [map_add, hz, hw]

variable (r : S[T;T⁻¹])
  (hr : r ^ 2 + laurentSlopeLinear (W.map (algebraMap R S)) (algebraMap R S b3) * r =
    laurentSlopeConstant (W.map (algebraMap R S)) (algebraMap R S s)
      (algebraMap R S b4) (algebraMap R S b6))

/-- Evaluate the entire original initial tensor chart using its own Laurent equation. -/
def tensorLaurentSlopeEvaluation : T₀ →ₐ[S] S[T;T⁻¹] :=
  (laurentSlopeEvaluation (W.map (algebraMap R S)) (algebraMap R S s)
    (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) r hr).comp
      (baseChangeEquiv W s b3 b4 b6 S).toAlgHom

/-- Original tensor incidence maps to the inverse original edge parameter. -/
theorem tensorLaurentSlopeEvaluation_t :
    tensorLaurentSlopeEvaluation W s b3 b4 b6 S r hr ((1 : S) ⊗ₜ[R] t W s b3 b4 b6) =
      LaurentPolynomial.T (-1) := by
  change laurentSlopeEvaluation _ _ _ _ _ r hr (baseChangeEquiv W s b3 b4 b6 S _) = _
  rw [baseChangeEquiv_t, laurentSlopeEvaluation_t]

/-- Original tensor slope maps to the full initial Laurent root. -/
theorem tensorLaurentSlopeEvaluation_v :
    tensorLaurentSlopeEvaluation W s b3 b4 b6 S r hr ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) = r := by
  change laurentSlopeEvaluation _ _ _ _ _ r hr (baseChangeEquiv W s b3 b4 b6 S _) = _
  rw [baseChangeEquiv_v, laurentSlopeEvaluation_v]

end FLT.Mazur.WeierstrassModificationX
