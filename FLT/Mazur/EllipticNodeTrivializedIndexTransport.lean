/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTrivializedChartGeometry
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensor

/-!
# Stage transport retains the arithmetic Laurent coordinates

Rewriting the terminal stage index preserves each original arithmetic chart,
including its residue unit. These identities compare maps into the actual
coefficient model rather than only their images.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (r : (ResidueField A)ˣ)
  {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (he : a = b) (hk0 : 0 < start + a)
local notation "F" => ResidueField A
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data F ha hb he)

/-- Positive terminal coordinate functions are unchanged by equality of stage indices. -/
@[reassoc] theorem nodeTrivializedPositiveChart_index_transport
    (hp : 2 * (start + a) < depth) :
    nodeTrivializedPositiveChart A hπ data D r a ha hk0 hp ≫ t =
      nodeTrivializedPositiveChart A hπ data D r b hb (by omega) (by omega) := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

/-- Negative terminal coordinate functions are unchanged by equality of stage indices. -/
@[reassoc] theorem nodeTrivializedNegativeChart_index_transport
    (hp : 2 * (start + a) < depth) :
    nodeTrivializedNegativeChart A hπ data D r a ha hk0 hp ≫ t =
      nodeTrivializedNegativeChart A hπ data D r b hb (by omega) (by omega) := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

/-- The middle arithmetic torus is unchanged by equality of stage indices. -/
@[reassoc] theorem nodeTrivializedMiddleChart_index_transport
    (hp : 2 * (start + a) = depth) :
    nodeTrivializedMiddleChart A hπ data D r a ha hk0 hp ≫ t =
      nodeTrivializedMiddleChart A hπ data D r b hb (by omega) (by omega) := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
