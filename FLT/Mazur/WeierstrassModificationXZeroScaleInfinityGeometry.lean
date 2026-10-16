/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroScaleInfinityEvaluation

/-!
# The actual zero-scale tensor boundary and its original overlap inclusion

The full boundary comparison is an isomorphism, retaining its entire original
initial-chart inclusion. Its composition with the actual node-boundary
isomorphism is the explicit evaluation of original tensor functions.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (hs : algebraMap R S s = 0)
local notation "V" => W.map (algebraMap R S)
local notation "c3" => algebraMap R S b3
local notation "c4" => algebraMap R S b4
local notation "c6" => algebraMap R S b6
local notation "y" => WeierstrassModificationX.y W s b3 b4 b6

/-- The full original tensor initial chart is the scale-zero coefficient chart. -/
def zeroScaleInitialIso : Spec (.of (Coordinate V 0 c3 c4 c6)) ≅
    Spec (.of (ScalarExtension W s b3 b4 b6 S)) :=
  Scheme.Spec.mapIso
    (zeroScaleBaseChangeEquiv W s b3 b4 b6 S hs).toRingEquiv.toCommRingCatIso.op

/-- The complete original tensor infinity boundary retains its exact zero-scale equation. -/
def zeroScaleInfinityBoundaryIso :
    Spec (.of (Localization.Away (WeierstrassModificationX.y V 0 c3 c4 c6))) ≅
    Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R] y))) :=
  Scheme.Spec.mapIso
    (zeroScaleInfinityBoundaryEquiv W s b3 b4 b6 S hs).toRingEquiv.toCommRingCatIso.op

/-- The boundary isomorphism preserves the entire original initial-chart inclusion. -/
@[reassoc] theorem zeroScaleInfinityBoundaryIso_inclusion :
    (zeroScaleInfinityBoundaryIso W s b3 b4 b6 S hs).hom ≫
      PrincipalOpenTensor.inclusion S y =
        polynomialInitialInfinityInclusion V 0 c3 c4 c6 ≫
          (zeroScaleInitialIso W s b3 b4 b6 S hs).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext
    (RingHom.ext (zeroScaleInfinityBoundaryEquiv_base W s b3 b4 b6 S hs))

variable (r : S[X])
  (hr : r ^ 2 + polynomialSlopeLinear (W.map (algebraMap R S)) (algebraMap R S b3) * r =
    polynomialSlopeConstant (W.map (algebraMap R S)) (algebraMap R S b4) (algebraMap R S b6))
  (I : Ideal S) (hI : IsNilpotent I) (hrI : r ∈ I.map C)
  (hc3 : algebraMap R S b3 ∈ I) (hbot : I = ⊥)

/-- The explicit tensor evaluation is the composition of the two original boundary isomorphisms. -/
theorem zeroScaleNodeInfinityEvaluation_spec :
    Spec.map (CommRingCat.ofHom (zeroScaleNodeInfinityEvaluation W s b3 b4 b6 S hs
      r hr I hI hrI hc3 hbot).toRingHom) =
        (polynomialNodeOverlapInfinityIso V 0 c3 c4 c6 r hr I hI hrI hc3).hom ≫
          (zeroScaleInfinityBoundaryIso W s b3 b4 b6 S hs).hom := by
  rw [← polynomialZeroNodeInfinityPullback_spec V c3 c4 c6 r hr I hI hrI hc3 hbot]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
