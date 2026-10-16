/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialInfinityParameter

/-!
# The complete Laurent infinity chart with the original tangent orientation

The ordered infinity tangent is reciprocal to the first fractional node
coordinate. Inverting the Laurent parameter gives its full polygon open
immersion and the exact square with the original y-boundary localization.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (k : ℕ)
local instance zeroInfinityPolygon_nilpotent : Fact (IsNilpotent (0 : R)) := ⟨1, by simp⟩

/-- The complete ordered Laurent infinity chart embeds along the edge between the initial nodes. -/
def zeroInfinityPolygonMap : branchTorus R ⟶
    PolygonInfinitesimal.scheme R 0 (2 * k + 3) (by omega) :=
  (edgeInversion R).hom ≫ rightBranchOpen R 0 ≫
    PolygonInfinitesimal.chart R 0 (2 * k + 3) (by omega) (initialPolygonIndex k false)

instance zeroInfinityPolygonMap_isOpenImmersion :
    IsOpenImmersion (zeroInfinityPolygonMap (R := R) k) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _ ≫ _))

/-- The full infinity torus preserves the original coefficient structure. -/
@[reassoc] theorem zeroInfinityPolygonMap_structure :
    zeroInfinityPolygonMap (R := R) k ≫
      PolygonInfinitesimal.toBase R 0 (2 * k + 3) (by omega) =
        Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R))) := by
  rw [zeroInfinityPolygonMap, Category.assoc, Category.assoc,
    PolygonInfinitesimal.chart_toBase, rightBranchOpen_base, edgeInversion_base]

variable (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I) (hbot : I = ⊥)
local notation "P" => zeroInitialInfinityParameter W b3 b4 b6 r hr I hI hrI h3
local notation "f" => zeroInitialAffinePolygonMap W ha k b3 b4 b6 r hr I hI hrI h3 hbot

/-- The original y-boundary uses the ordered reciprocal infinity parameter on the entire torus. -/
@[reassoc] theorem zeroInitialAffinePolygonMap_full_infinity_boundary :
    polynomialInitialInfinityInclusion W 0 b3 b4 b6 ≫ f =
      P ≫ (edgeInversion R).hom ≫ zeroInfinityPolygonMap (R := R) k := by
  rw [zeroInfinityPolygonMap, ← Category.assoc (edgeInversion R).hom,
    show (edgeInversion R).hom ≫ (edgeInversion R).hom = 𝟙 _ from
      (edgeInversion R).hom_inv_id, Category.id_comp]
  exact zeroInitialAffinePolygonMap_infinity_boundary W ha k b3 b4 b6 r hr I hI hrI h3 hbot

end FLT.Mazur.WeierstrassDividedDepth
