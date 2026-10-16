/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialInfinityTransition
public import FLT.Mazur.WeierstrassDividedZeroInfinityPolygon
public import FLT.Mazur.WeierstrassModificationXZeroScaleInfinityGeometry
public import FLT.Mazur.WeierstrassModificationXZeroScaleLaurentNormalization

/-!
# The original finite-model infinity normalization square on the zero fiber

The actual original y-boundary attachment, followed by the existing full
Laurent infinity normalization, is the reciprocal original tangent parameter.
Consequently the entire original initial affine comparison and infinity
polygon chart commute on their actual finite-model intersection.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassIntegralChart PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth)
  (j : ℕ) (hj : j ≤ n) (hs : residue R (π ^ start) = 0)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "b3" => Data.b3 d
local notation "b4" => Data.b4 d
local notation "b6" => Data.b6 d
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "c3" => residue R b3
local notation "c4" => residue R b4
local notation "c6" => residue R b6
variable (r : (ResidueField R)[X])
  (hr : r ^ 2 + polynomialSlopeLinear (W.map (residue R))
    (residue R (Data.b3 (data (Fin.mk 0 (Nat.zero_lt_succ n))))) * r =
      polynomialSlopeConstant (W.map (residue R))
        (residue R (Data.b4 (data (Fin.mk 0 (Nat.zero_lt_succ n)))))
        (residue R (Data.b6 (data (Fin.mk 0 (Nat.zero_lt_succ n))))))
  (I : Ideal (ResidueField R)) (hI : IsNilpotent I) (hrI : r ∈ I.map C)
  (hc3 : residue R (Data.b3 (data (Fin.mk 0 (Nat.zero_lt_succ n)))) ∈ I) (hbot : I = ⊥)
local notation "E" => zeroScaleInfinityBoundaryIso W (π ^ start) b3 b4 b6 K hs
local notation "e" => polynomialNodeOverlapInfinityIso V 0 c3 c4 c6 r hr I hI hrI hc3
local notation "t" => initialGlobalYToInfinity hπ data K j hj
local notation "P" => zeroInitialInfinityParameter V c3 c4 c6 r hr I hI hrI hc3

include hbot

/-- The actual finite-model infinity normalization is the reciprocal original boundary parameter. -/
@[reassoc] theorem zeroOriginalInfinity_normalization :
    (E).hom ≫ t ≫ (infinityResidueIso D hdepth).inv = P ≫ (edgeInversion K).hom := by
  apply (cancel_epi (e).hom).mp
  rw [zeroInitialInfinityParameter_overlap_assoc, initialGlobalYToInfinity_eq_spec]
  rw [← Category.assoc]
  erw [← zeroScaleNodeInfinityEvaluation_spec
    W (π ^ start) b3 b4 b6 K hs r hr I hI hrI hc3 hbot]
  exact zeroScaleNodeInfinityEvaluation_normalization D hdepth (π ^ start) b3 b4 b6 hs
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) r hr I hI hrI hc3 hbot

variable (ha : IsUnit (W.map (residue R)).a₁) (k : ℕ)
local instance zeroOriginalInfinity_nilpotent : Fact (IsNilpotent (0 : K)) := ⟨1, by simp⟩
local notation "F" => zeroInitialAffinePolygonMap V ha k c3 c4 c6 r hr I hI hrI hc3 hbot

/-- The full original initial affine map commutes with the actual normalized infinity chart. -/
@[reassoc] theorem zeroOriginalInfinity_polygon_square :
    polynomialInitialInfinityInclusion V 0 c3 c4 c6 ≫ F =
      (E).hom ≫ t ≫ (infinityResidueIso D hdepth).inv ≫
        zeroInfinityPolygonMap (R := K) k := by
  rw [zeroInitialAffinePolygonMap_full_infinity_boundary,
    zeroOriginalInfinity_normalization_assoc hπ data D hdepth j hj hs r hr I hI hrI hc3 hbot]

/-- The same square holds on the original tensor localization, before zero-scale transport. -/
@[reassoc] theorem zeroOriginalInfinity_tensor_polygon_square :
    PrincipalOpenTensor.inclusion K (WeierstrassModificationX.y W (π ^ start) b3 b4 b6) ≫
      (zeroScaleInitialIso W (π ^ start) b3 b4 b6 K hs).inv ≫ F =
        t ≫ (infinityResidueIso D hdepth).inv ≫ zeroInfinityPolygonMap (R := K) k := by
  apply (cancel_epi (E).hom).mp
  rw [zeroScaleInfinityBoundaryIso_inclusion_assoc, Iso.hom_inv_id_assoc]
  exact zeroOriginalInfinity_polygon_square hπ data D hdepth j hj hs r hr I hI hrI hc3 hbot ha k

end FLT.Mazur.WeierstrassDividedDepth
