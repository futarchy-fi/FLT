/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTrivializedMiddleChart
public import FLT.Mazur.LaurentScaledCoordinateIsomorphisms

/-!
# The trivialized charts preserve the actual geometric presentations

All three coordinate substitutions are open immersions into the original
finite model and preserve its exact residue-field structure map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (r : (ResidueField A)ˣ)
  (j : ℕ) (hj : j ≤ n) (hk0 : 0 < start + j)
local notation "F" => ResidueField A
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A F))
local notation "base" => pullback.fst q (finiteGlobalStructure hπ data j hj)

/-- Positive trivialization is an actual open immersion in the original finite model. -/
instance nodeTrivializedPositiveChart_isOpenImmersion (hp : 2 * (start + j) < depth) :
    IsOpenImmersion (nodeTrivializedPositiveChart A hπ data D r j hj hk0 hp) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _ ≫ _))

/-- Negative trivialization is an actual open immersion in the original finite model. -/
instance nodeTrivializedNegativeChart_isOpenImmersion (hp : 2 * (start + j) < depth) :
    IsOpenImmersion (nodeTrivializedNegativeChart A hπ data D r j hj hk0 hp) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _ ≫ _))

/-- Middle trivialization preserves the entire original open torus. -/
instance nodeTrivializedMiddleChart_isOpenImmersion (hm : 2 * (start + j) = depth) :
    IsOpenImmersion (nodeTrivializedMiddleChart A hπ data D r j hj hk0 hm) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The positive chart keeps the original residue coefficient map. -/
@[reassoc] theorem nodeTrivializedPositiveChart_structure (hp : 2 * (start + j) < depth) :
    nodeTrivializedPositiveChart A hπ data D r j hj hk0 hp ≫ base =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [nodeTrivializedPositiveChart, Category.assoc, Category.assoc,
    terminalNodeChart_structure, PolygonNodeBranches.right_toBase]
  exact PolygonScaledReciprocal.scaling_spec_structure _

/-- The negative chart keeps the original residue coefficient map. -/
@[reassoc] theorem nodeTrivializedNegativeChart_structure (hp : 2 * (start + j) < depth) :
    nodeTrivializedNegativeChart A hπ data D r j hj hk0 hp ≫ base =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [nodeTrivializedNegativeChart, Category.assoc, Category.assoc,
    terminalNodeChart_structure, PolygonNodeBranches.left_toBase]
  exact PolygonScaledReciprocal.reciprocal_spec_structure _

/-- The middle chart keeps the original residue coefficient map. -/
@[reassoc] theorem nodeTrivializedMiddleChart_structure (hm : 2 * (start + j) = depth) :
    nodeTrivializedMiddleChart A hπ data D r j hj hk0 hm ≫ base =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [nodeTrivializedMiddleChart, Category.assoc, terminalLaurentChart_structure]
  exact PolygonScaledReciprocal.reciprocal_spec_structure _

end FLT.Mazur.WeierstrassDividedDepth
