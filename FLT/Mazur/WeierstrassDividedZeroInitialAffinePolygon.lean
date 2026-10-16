/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroMobiusInitialOverlap
public import FLT.Mazur.WeierstrassModificationXPolynomialNodeCover

/-!
# The full original initial affine scheme maps to the complete zero polygon

The actual fractional charts glue across their original overlap. The source
is the entire original initial affine scheme, and both cyclic labels and
its arithmetic structure map are retained.
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
local instance zeroInitialAffine_nilpotent : Fact (IsNilpotent (0 : R)) := ⟨1, by simp⟩
local notation "A" => Coordinate W 0 b3 b4 b6
local notation "C" => polynomialNodeOpenCover W 0 b3 b4 b6 r hr I hI hrI h3 ha
local notation "F" => polynomialNodeChart W 0 b3 b4 b6 r hr I hI hrI h3
local notation "G" => polynomialOppositeNodeChart W 0 b3 b4 b6 r hr I hI hrI h3

/-- The two full original fractional charts glue to a map from the original affine scheme. -/
def zeroInitialAffinePolygonMap : Spec (.of A) ⟶
    PolygonInfinitesimal.scheme R 0 (2 * k + 3) (by omega) :=
  (C).glueMorphisms (zeroInitialMobiusPolygonMap W ha k)
    (polynomialNodeOpenCover_compatible W 0 b3 b4 b6 r hr I hI hrI h3 ha
      (zeroInitialMobiusPolygonMap W ha k)
      (zeroInitialMobiusPolygonMap_original_overlap W ha k b3 b4 b6 r hr I hI hrI h3 hbot))

local notation "f" => zeroInitialAffinePolygonMap W ha k b3 b4 b6 r hr I hI hrI h3 hbot

/-- Both original full node charts retain their actual labeled polygon embeddings. -/
@[reassoc] theorem zeroInitialAffinePolygonMap_chart (b : Bool) :
    (if b then G else F) ≫ f = zeroInitialMobiusPolygonMap W ha k b :=
  (C).ι_glueMorphisms _ _ b

/-- The full original initial affine comparison preserves its original coefficient structure. -/
@[reassoc] theorem zeroInitialAffinePolygonMap_structure :
    f ≫ PolygonInfinitesimal.toBase R 0 (2 * k + 3) (by omega) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  apply (C).hom_ext
  intro b
  change Bool at b
  rw [← Category.assoc]
  change ((if b then G else F) ≫ f) ≫ _ = _
  rw [zeroInitialAffinePolygonMap_chart, zeroInitialMobiusPolygonMap_base]
  cases b
  · exact (polynomialNodeChart_structure W 0 b3 b4 b6 r hr I hI hrI h3).symm
  · exact (polynomialOppositeNodeChart_structure W 0 b3 b4 b6 r hr I hI hrI h3).symm

end FLT.Mazur.WeierstrassDividedDepth
