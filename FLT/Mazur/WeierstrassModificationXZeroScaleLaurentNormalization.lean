/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroScaleInfinityEvaluation
public import FLT.Mazur.WeierstrassInfinityResidueGeometry
public import FLT.Mazur.WeierstrassModificationXZeroMobiusOverlapBoundary

/-!
# The actual residue infinity normalization has the reciprocal original parameter

The Laurent equivalence of the original infinity tensor chart is evaluated
on the entire original node intersection. Its full map, not only a residue
coordinate identity, is the reciprocal original tangent-ratio parameter.
-/

@[expose] public noncomputable section
open Polynomial IsLocalRing AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (s b3 b4 b6 : R) (hs : residue R s = 0)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "c3" => residue R b3
local notation "c4" => residue R b4
local notation "c6" => residue R b6
variable (r : (ResidueField R)[X])
  (hr : r ^ 2 + polynomialSlopeLinear (W.map (residue R))
    (residue R b3) * r =
      polynomialSlopeConstant (W.map (residue R))
        (residue R b4) (residue R b6))
  (I : Ideal (ResidueField R)) (hI : IsNilpotent I) (hrI : r ∈ I.map C)
  (hc3 : residue R b3 ∈ I) (hbot : I = ⊥)
local notation "O" => PolynomialNodeOverlap V 0
local notation "H" => zeroScaleNodeInfinityEvaluation W s b3 b4 b6 K hs r hr I hI hrI hc3 hbot
local notation "f" => initialInfinityTensorTransition W s b3 b4 b6 h3 h4 h6 K
local notation "v" => polynomialNodeOverlapRatio V 0 c3 c4 c6 r hr I hI hrI hc3
open WeierstrassIntegralChart

/-- The actual original Laurent infinity normalization evaluated on the full node overlap. -/
def zeroScaleNodeLaurentNormalization : K[T;T⁻¹] →ₐ[K] O :=
  ((H).comp f).comp (infinityResidueEquiv D hdepth).symm.toAlgHom

local notation "L" => zeroScaleNodeLaurentNormalization D hdepth s b3 b4 b6 hs h3 h4 h6
  r hr I hI hrI hc3 hbot

/-- Its positive generator is the reciprocal original full tangent ratio. -/
theorem zeroScaleNodeLaurentNormalization_T : L (LaurentPolynomial.T 1) = (↑((v)⁻¹) : O) := by
  change H (f ((infinityResidueEquiv D hdepth).symm (LaurentPolynomial.T 1))) = _
  rw [infinityResidueEquiv_symm_tangent]
  exact zeroScaleNodeInfinityEvaluation_tangent W s b3 b4 b6 K hs r hr I hI hrI hc3 hbot
    h3 h4 h6

/-- The complete original Laurent normalization is evaluation at the reciprocal full ratio. -/
theorem zeroScaleNodeLaurentNormalization_eq_evalUnit :
    L = LaurentUnitPoints.evalUnit ((v)⁻¹) := by
  have h : LaurentUnitPoints.pointUnit L = (v)⁻¹ := by
    apply Units.ext
    exact zeroScaleNodeLaurentNormalization_T D hdepth s b3 b4 b6 hs h3 h4 h6
      r hr I hI hrI hc3 hbot
  rw [← LaurentUnitPoints.evalUnit_pointUnit L, h]

/-- The actual infinity normalization square has the required original reciprocal orientation. -/
@[reassoc] theorem zeroScaleNodeInfinityEvaluation_normalization :
    Spec.map (CommRingCat.ofHom (H).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ (infinityResidueIso D hdepth).inv =
        zeroMobiusOverlapParameter V c3 c4 c6 r hr I hI hrI hc3 ≫
          (PolygonSmoothing.edgeInversion K).hom := by
  unfold zeroMobiusOverlapParameter
  rw [← NodalFiber.unitParameter_inverse]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom
    (zeroScaleNodeLaurentNormalization_eq_evalUnit D hdepth s b3 b4 b6 hs h3 h4 h6
      r hr I hI hrI hc3 hbot)

end FLT.Mazur.WeierstrassModificationX
