/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedTrivializedCharts
public import FLT.Mazur.LaurentScaledCoordinateIsomorphisms

/-!
# Geometry of the retained trivialized charts

The arithmetic changes of coordinate retain open immersions and the original
coefficient projections at every later stage of the finite resolution.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (r : (ResidueField A)ˣ)
  (j : ℕ) (hj : j + 1 ≤ n) (t : ℕ) (ht : j + 1 + t ≤ n)
  (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
local notation "F" => ResidueField A
local notation "base" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A F)))
  (finiteGlobalStructure hπ data (j + 1 + t) ht)

instance retainedTrivializedPositiveChart_isOpenImmersion :
    IsOpenImmersion (retainedTrivializedPositiveChart A hπ data D r j hj t ht hk0 hp) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance retainedTrivializedNegativeChart_isOpenImmersion :
    IsOpenImmersion (retainedTrivializedNegativeChart A hπ data D r j hj t ht hk0 hp) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The positive arithmetic chart retains the original coefficient spectrum. -/
@[reassoc] theorem retainedTrivializedPositiveChart_structure :
    retainedTrivializedPositiveChart A hπ data D r j hj t ht hk0 hp ≫ base =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [retainedTrivializedPositiveChart, Category.assoc, retainedPositiveLaurentChart_structure]
  exact PolygonScaledReciprocal.scaling_spec_structure _

/-- The negative arithmetic chart retains the original coefficient spectrum. -/
@[reassoc] theorem retainedTrivializedNegativeChart_structure :
    retainedTrivializedNegativeChart A hπ data D r j hj t ht hk0 hp ≫ base =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [retainedTrivializedNegativeChart, Category.assoc, retainedNegativeLaurentChart_structure]
  exact PolygonScaledReciprocal.reciprocal_spec_structure _

end FLT.Mazur.WeierstrassDividedDepth
