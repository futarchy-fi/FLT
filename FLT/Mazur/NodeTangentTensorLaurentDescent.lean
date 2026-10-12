/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentTensorOpen
public import FLT.Mazur.PolygonScalingNaturality

/-!
# The full semilinear Laurent formula on the original tangent open

The actual localized chart operation corresponds to coefficient conjugation
and inversion of the Laurent parameter. This retains the entire coefficient
map and universal coordinate, rather than only rational point values.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (x y : A)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "B" => S ⊗[R] A
local notation "U" => nodeTangentTensorOpen W x y
local notation "σ" => nodeTangentTensorOpenConjugation W x y
local notation "t" => nodeTangentTensorOpenParameter W x y

/-- The localized operation keeps the original coefficient inclusion, semilinearly. -/
theorem nodeTangentTensorOpenConjugation_coeff (c : S) :
    σ (algebraMap S U c) = algebraMap S U (nodeTangentConjugation W c) := by
  rw [IsScalarTower.algebraMap_apply S B U,
    nodeTangentTensorOpenConjugation_algebraMap, IsScalarTower.algebraMap_apply S B U]
  congr 1

/-- The entire Laurent algebra map determined by the constructed tangent ratio. -/
def nodeTangentTensorLaurentParameter : S[T;T⁻¹] →+* U :=
  LaurentPolynomial.eval₂ (algebraMap S U) t

/-- Conjugate coefficients and reverse the Laurent coordinate simultaneously. -/
def nodeTangentLaurentTwist : S[T;T⁻¹] →+* S[T;T⁻¹] :=
  LaurentPolynomial.invert.toRingHom.comp
    (PolygonScalingNaturality.coeffMap (nodeTangentConjugation W).toRingHom)

/-- The semilinear Laurent operation retains exactly the adjoined coefficient conjugation. -/
@[simp] theorem nodeTangentLaurentTwist_C (c : S) :
    nodeTangentLaurentTwist W (LaurentPolynomial.C c) =
      LaurentPolynomial.C (nodeTangentConjugation W c) := by
  simp [nodeTangentLaurentTwist]

/-- The universal torus coordinate is inverted by the same semilinear operation. -/
@[simp] theorem nodeTangentLaurentTwist_T_one :
    nodeTangentLaurentTwist W (LaurentPolynomial.T 1) = LaurentPolynomial.T (-1) := by
  simp [nodeTangentLaurentTwist]

/-- The inverse universal coordinate returns to the original coordinate. -/
@[simp] theorem nodeTangentLaurentTwist_T_neg_one :
    nodeTangentLaurentTwist W (LaurentPolynomial.T (-1)) = LaurentPolynomial.T 1 := by
  simp [nodeTangentLaurentTwist]

/-- The original localized chart realizes the full semilinear parameter formula. -/
theorem nodeTangentTensorLaurentParameter_conjugate :
    (σ).comp (nodeTangentTensorLaurentParameter W x y) =
      (nodeTangentTensorLaurentParameter W x y).comp (nodeTangentLaurentTwist W) := by
  have ht := congrArg Units.val (nodeTangentTensorOpenParameter_conjugate W x y)
  have hti := congrArg (fun z : Uˣ => (z⁻¹ : Uˣ).val)
    (nodeTangentTensorOpenParameter_conjugate W x y)
  apply PolygonScalingNaturality.ringHom_ext
  · intro c
    simpa only [RingHom.comp_apply, nodeTangentTensorLaurentParameter,
      LaurentPolynomial.eval₂_C, nodeTangentLaurentTwist_C] using
      nodeTangentTensorOpenConjugation_coeff W x y c
  · simpa [nodeTangentTensorLaurentParameter] using ht
  · simpa [nodeTangentTensorLaurentParameter] using hti

/-- The corresponding square commutes as actual morphisms of affine schemes. -/
theorem nodeTangentTensorLaurentParameter_spec :
    Spec.map (CommRingCat.ofHom σ) ≫
        Spec.map (CommRingCat.ofHom (nodeTangentTensorLaurentParameter W x y)) =
      Spec.map (CommRingCat.ofHom (nodeTangentTensorLaurentParameter W x y)) ≫
        Spec.map (CommRingCat.ofHom (nodeTangentLaurentTwist W)) := by
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using
    congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (nodeTangentTensorLaurentParameter_conjugate W x y)

end FLT.Mazur
