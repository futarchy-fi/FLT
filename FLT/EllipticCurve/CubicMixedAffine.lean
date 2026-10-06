/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicMixedCover

/-! # The affine-input piece of the mixed-chart addition cover -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The mixed input chart restricted to finite first inputs. -/
abbrev MixedAffineRing := Localization.Away (mixedFirstZ W)

/-- Restriction to the finite-input part of the mixed chart. -/
def mixedAffineRestriction : ChartPairRing W true false →ₐ[R] MixedAffineRing W :=
  IsScalarTower.toAlgHom R (ChartPairRing W true false) (MixedAffineRing W)

/-- First input in its original infinity chart. -/
def mixedAffineLeft : Ring W true →ₐ[R] MixedAffineRing W :=
  (mixedAffineRestriction W).comp Algebra.TensorProduct.includeLeft

/-- Second input, already in the ordinary affine chart. -/
def mixedAffineRight : Ring W false →ₐ[R] MixedAffineRing W :=
  (mixedAffineRestriction W).comp Algebra.TensorProduct.includeRight

/-- The first input factors through the chart overlap. -/
def mixedAffineOverlap : Overlap W true →ₐ[R] MixedAffineRing W :=
  IsLocalization.Away.liftAlgHom (coord W true 1) (f := mixedAffineLeft W)
    (isUnit_iff_exists_inv.mpr ⟨IsLocalization.Away.invSelf (mixedFirstZ W),
      IsLocalization.Away.mul_invSelf (S := MixedAffineRing W) (mixedFirstZ W)⟩)

theorem mixedAffineOverlap_loc (i : Fin 2) :
    mixedAffineOverlap W (loc W true i) = mixedAffineLeft W (coord W true i) := by
  simp [mixedAffineOverlap, loc, IsLocalization.Away.liftAlgHom_apply]

theorem mixedAffineOverlap_inv :
    mixedAffineOverlap W (inv W true) = IsLocalization.Away.invSelf (mixedFirstZ W) := by
  have h := congrArg (mixedAffineOverlap W) (loc_mul_inv W true)
  rw [map_mul, mixedAffineOverlap_loc, map_one] at h
  have h' := IsLocalization.Away.mul_invSelf (S := MixedAffineRing W) (mixedFirstZ W)
  change mixedAffineLeft W (coord W true 1) *
    IsLocalization.Away.invSelf (mixedFirstZ W) = 1 at h'
  linear_combination IsLocalization.Away.invSelf (mixedFirstZ W) * h -
    mixedAffineOverlap W (inv W true) * h'

/-- The first input converted to ordinary affine coordinates. -/
def mixedAffineFirst : Ring W false →ₐ[R] MixedAffineRing W :=
  (mixedAffineOverlap W).comp (changeChart W true)

@[simp] theorem mixedAffineFirst_coord_zero :
    mixedAffineFirst W (coord W false 0) =
      mixedAffineLeft W (coord W true 0) * IsLocalization.Away.invSelf (mixedFirstZ W) := by
  change mixedAffineOverlap W (changeChart W true (coord W (!true) 0)) = _
  rw [changeChart_coord]
  change mixedAffineOverlap W (loc W true 0 * inv W true) = _
  rw [map_mul, mixedAffineOverlap_loc, mixedAffineOverlap_inv]

@[simp] theorem mixedAffineFirst_coord_one :
    mixedAffineFirst W (coord W false 1) =
      IsLocalization.Away.invSelf (mixedFirstZ W) := by
  change mixedAffineOverlap W (changeChart W true (coord W (!true) 1)) = _
  rw [changeChart_coord]
  exact mixedAffineOverlap_inv W

/-- Both finite inputs, as a map from the ordinary chart product. -/
def mixedAffineInputs : AffinePairRing W →ₐ[R] MixedAffineRing W :=
  Algebra.TensorProduct.productMap (mixedAffineFirst W) (mixedAffineRight W)

/-- The existing affine addition pulled back to the first piece of the mixed cover. -/
def mixedAffineAddition [W.IsElliptic] : Spec (.of (MixedAffineRing W)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (mixedAffineInputs W).toRingHom) ≫ affineAddition W

@[reassoc (attr := simp)] theorem mixedAffineAddition_toBase [W.IsElliptic] :
    mixedAffineAddition W ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (MixedAffineRing W))) := by
  unfold mixedAffineAddition
  rw [Category.assoc, affineAddition_toBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (mixedAffineInputs W).comp_algebraMap

end WeierstrassCurve.CubicCharts
