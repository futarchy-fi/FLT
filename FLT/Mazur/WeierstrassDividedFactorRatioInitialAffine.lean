/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioInitialOverlap
public import FLT.Mazur.WeierstrassModificationXPolynomialNodeCover

/-!
# The full original initial affine scheme in the corrected arithmetic polygon

The complete corrected node charts glue along their actual original overlap
at arbitrary nilpotent order. The normalized smoothing is retained exactly.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) [Fact (IsNilpotent τ)] (k : ℕ)
  (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "C" => polynomialNodeOpenCover W s b3 b4 b6 r hr I hI hrI h3 ha
local notation "F" => polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "G" => polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3

/-- The two full original corrected charts glue to a map from the original affine scheme. -/
def factorRatioInitialAffinePolygonMap : Spec (.of A) ⟶
    PolygonInfinitesimal.scheme R τ (2 * k + 3) (by omega) :=
  (C).glueMorphisms (factorRatioInitialPolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3)
    (polynomialNodeOpenCover_compatible W s b3 b4 b6 r hr I hI hrI h3 ha
      (factorRatioInitialPolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3)
      (factorRatioInitialPolygonMap_original_overlap τ k W ha s hτ b3 b4 b6 r hr I hI hrI h3))

local notation "f" => factorRatioInitialAffinePolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3

/-- Both original full node charts retain their actual labeled polygon embeddings. -/
@[reassoc] theorem factorRatioInitialAffinePolygonMap_chart (b : Bool) :
    (if b then G else F) ≫ f =
      factorRatioInitialPolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI h3 b :=
  (C).ι_glueMorphisms _ _ b

/-- The full original initial affine comparison preserves its original coefficient structure. -/
@[reassoc] theorem factorRatioInitialAffinePolygonMap_structure :
    f ≫ PolygonInfinitesimal.toBase R τ (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  apply (C).hom_ext
  intro b
  change Bool at b
  rw [← Category.assoc]
  change ((if b then G else F) ≫ f) ≫ _ = _
  rw [factorRatioInitialAffinePolygonMap_chart, factorRatioInitialPolygonMap_base]
  cases b
  · exact (polynomialNodeChart_structure W s b3 b4 b6 r hr I hI hrI h3).symm
  · exact (polynomialOppositeNodeChart_structure W s b3 b4 b6 r hr I hI hrI h3).symm

end FLT.Mazur.WeierstrassDividedDepth
