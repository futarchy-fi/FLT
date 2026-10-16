/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialAffinePolygon
public import FLT.Mazur.WeierstrassModificationXNodeOverlapInfinityIso

/-!
# The original zero-fiber infinity boundary has its actual polygon parameter

Transporting the full tangent ratio across the original y-open comparison
identifies the restriction of the entire initial affine polygon map. The
source is the original infinity-boundary localization, not a replacement torus.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (k : ℕ)
  (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I) (hbot : I = ⊥)
local instance zeroInitialInfinity_nilpotent : Fact (IsNilpotent (0 : R)) := ⟨1, by simp⟩
local notation "Y" => Localization.Away (y W 0 b3 b4 b6)
local notation "e" => polynomialNodeOverlapInfinityIso W 0 b3 b4 b6 r hr I hI hrI h3
local notation "P" => zeroMobiusOverlapParameter W b3 b4 b6 r hr I hI hrI h3
local notation "f" => zeroInitialAffinePolygonMap W ha k b3 b4 b6 r hr I hI hrI h3 hbot

/-- The full tangent-ratio Laurent parameter on the original y-infinity boundary. -/
def zeroInitialInfinityParameter : Spec (.of Y) ⟶ branchTorus R := (e).inv ≫ P

/-- The original node intersection pulls the infinity parameter back to the exact full ratio. -/
@[reassoc] theorem zeroInitialInfinityParameter_overlap :
    (e).hom ≫ zeroInitialInfinityParameter W b3 b4 b6 r hr I hI hrI h3 = P := by
  rw [zeroInitialInfinityParameter, Iso.hom_inv_id_assoc]

/-- The full original affine comparison has this exact boundary in its first initial label. -/
@[reassoc] theorem zeroInitialAffinePolygonMap_infinity_boundary :
    polynomialInitialInfinityInclusion W 0 b3 b4 b6 ≫ f =
      zeroInitialInfinityParameter W b3 b4 b6 r hr I hI hrI h3 ≫ rightBranchOpen R 0 ≫
        PolygonInfinitesimal.chart R 0 (2 * k + 3) (by omega)
          (initialPolygonIndex k false) := by
  have hf : polynomialNodeChart W 0 b3 b4 b6 r hr I hI hrI h3 ≫ f =
      zeroInitialMobiusPolygonMap W ha k false :=
    zeroInitialAffinePolygonMap_chart W ha k b3 b4 b6 r hr I hI hrI h3 hbot false
  apply (cancel_epi (e).hom).mp
  rw [← Category.assoc, polynomialNodeOverlapInfinityIso_hom_inclusion,
    Category.assoc, hf]
  simp only [zeroInitialMobiusPolygonMap, Bool.false_eq_true, ↓reduceIte, Category.id_comp]
  rw [zeroInitialMobiusChart_overlap_first_assoc W ha b3 b4 b6 r hr I hI hrI h3 hbot,
    zeroInitialInfinityParameter_overlap_assoc]

end FLT.Mazur.WeierstrassDividedDepth
