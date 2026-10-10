/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueSlopeTransition
public import FLT.Mazur.WeierstrassInfinityResidueGeometry

/-!
# The original tangent Laurent parameter on the punctured slope line

Extend the actual infinity transition over the residue field, then transport
through the full infinity equivalence. Its positive generator is (v+a)/v,
with the ordered tangent coefficient and every original coefficient retained.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "P" => SlopeOpen a
local notation "z" => slopeZ a
local notation "A" => algebraMap K P a
open WeierstrassIntegralChart
local notation "I" => ChartScalarExtension K W 1
local notation "f" => residueSlopeInfinityMap D k hk0 hk b3 b4 b6 h3 h4 h6

/-- Extension of the actual original infinity transition over the original residue field. -/
def residueSlopeInfinityTensorMap : I →ₐ[K] P := AlgHom.liftEquiv R K _ _ f

/-- Every original infinity function keeps its value under the tensor extension. -/
theorem residueSlopeInfinityTensorMap_tmul (r : ResidueField R)
    (w : WeierstrassIntegralChart.Coordinate W 1) :
    residueSlopeInfinityTensorMap D k hk0 hk b3 b4 b6 h3 h4 h6 (r ⊗ₜ[R] w) = r • f w := rfl

/-- The actual tensor transition retains the original infinity coordinate projection. -/
@[reassoc] theorem residueSlopeInfinityTensorMap_projection :
    Spec.map (CommRingCat.ofHom
      (residueSlopeInfinityTensorMap D k hk0 hk b3 b4 b6 h3 h4 h6).toRingHom) ≫
        TensorOpenChart.projection = Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro w
  exact one_smul K (f w)

/-- The ordered Laurent transition is induced by the original infinity equivalence. -/
def residueSlopeLaurentMap : K[T;T⁻¹] →ₐ[K] P :=
  (residueSlopeInfinityTensorMap D k hk0 hk b3 b4 b6 h3 h4 h6).comp
    (infinityResidueEquiv D hdepth).symm.toAlgHom

/-- The original positive tangent parameter is (v+a)/v on the entire slope overlap. -/
theorem residueSlopeLaurentMap_T :
    residueSlopeLaurentMap D k hk0 hk b3 b4 b6 h3 h4 h6 hdepth (LaurentPolynomial.T 1) =
      (z + A) * ↑(slope_units a).1.unit⁻¹ := by
  change residueSlopeInfinityTensorMap D k hk0 hk b3 b4 b6 h3 h4 h6
    ((infinityResidueEquiv D hdepth).symm (LaurentPolynomial.T 1)) = _
  rw [infinityResidueEquiv_symm_tangent, map_add, map_one, map_mul, AlgHom.commutes]
  rw [infinityTensorCoord, residueSlopeInfinityTensorMap_tmul, one_smul,
    residueSlopeInfinityMap_x]
  have hz : z * ↑(slope_units a).1.unit⁻¹ = 1 :=
    Units.mul_inv_eq_one.mpr (slope_units a).1.unit_spec
  rw [add_mul, hz]

/-- Multiplication by the original slope gives the ordered second tangent factor. -/
theorem residueSlopeLaurentMap_T_mul :
    residueSlopeLaurentMap D k hk0 hk b3 b4 b6 h3 h4 h6 hdepth
      (LaurentPolynomial.T 1) * z = z + A := by
  rw [residueSlopeLaurentMap_T, mul_assoc,
    Units.inv_mul_eq_one.mpr (slope_units a).1.unit_spec, mul_one]

/-- The explicit Laurent transition is the tensor transition followed by normalization. -/
theorem residueSlopeLaurentMap_spec :
    Spec.map (CommRingCat.ofHom
      (residueSlopeLaurentMap D k hk0 hk b3 b4 b6 h3 h4 h6 hdepth).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (residueSlopeInfinityTensorMap D k hk0 hk b3 b4 b6 h3 h4 h6).toRingHom) ≫
        (infinityResidueIso D hdepth).inv := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
