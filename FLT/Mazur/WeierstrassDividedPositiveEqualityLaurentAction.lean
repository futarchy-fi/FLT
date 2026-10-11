/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientFaithful
public import FLT.Mazur.WeierstrassDividedPositiveEqualityIdentityAction

/-!
# Multiplicative coordinates for the actual residue identity action

The original Laurent coordinate multiplies under the integral action specialized
to the residue fiber. This comparison is on every scheme of points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "hd" => lt_of_lt_of_le
  (Nat.mul_pos (by decide : 0 < 2) (Nat.succ_pos (start + s))) hk
local notation "g" => infinityResidueSmoothGroupIso D hd
local notation "base" => pullback.fst
  (Spec.map (CommRingCat.ofHom (algebraMap R K))) (finiteGlobalStructure hπ data (s + 1) hs)
variable (T : Over (Spec (CommRingCat.of (ResidueField R))))

include D hk in
/-- An actual Laurent point in the retained residue identity chart. -/
def positiveEqualityLaurentOverPoint (a : T ⟶ MultiplicativeGroupScheme.gm K) :
    T ⟶ Over.mk base :=
  finiteGlobalSmoothCoefficientOverPoint hπ data (s + 1) hs K T
    (a ≫ (g).inv.hom.hom.hom)

/-- The Laurent point is exactly the point of the intrinsic smooth group in the finite model. -/
theorem positiveEqualityLaurentOverPoint_eq (a : T ⟶ MultiplicativeGroupScheme.gm K) :
    positiveEqualityLaurentOverPoint hπ data D s hs hk T a =
      finiteGlobalSmoothCoefficientOverPoint hπ data (s + 1) hs K T
        (a ≫ (g).inv.hom.hom.hom) := rfl

/-- The point map retains the original Laurent chart as an actual scheme morphism. -/
theorem positiveEqualityLaurentOverPoint_left (a : T ⟶ MultiplicativeGroupScheme.gm K) :
    (positiveEqualityLaurentOverPoint hπ data D s hs hk T a).left =
      a.left ≫ infinityLaurentChart hπ data D hd (s + 1) hs := by
  change (a.left ≫ (g).inv.hom.hom.hom.left) ≫
      finiteGlobalSmoothCoefficientEmbedding K hπ data (s + 1) hs = _
  rw [infinityResidueSmoothGroupIso_inv, Category.assoc,
    positiveEqualityInfinityLaurentChart_smoothEmbedding hπ data D s hs hk]

/-- Actual specialized translation is multiplication in the original Laurent coordinate. -/
theorem positiveEqualityLaurentOverPoint_action
    (a b : T ⟶ MultiplicativeGroupScheme.gm K) :
    (a ≫ (g).inv.hom.hom.hom) • positiveEqualityLaurentOverPoint hπ data D s hs hk T b =
      positiveEqualityLaurentOverPoint hπ data D s hs hk T (a * b) := by
  rw [positiveEqualityLaurentOverPoint_eq, positiveEqualityLaurentOverPoint_eq,
    finiteGlobalCoefficientOverPointAction_smooth, MonObj.mul_comp]

/-- Distinct Laurent points remain distinct on the whole modified residue fiber. -/
theorem positiveEqualityLaurentOverPoint_injective :
    Function.Injective (positiveEqualityLaurentOverPoint hπ data D s hs hk T) := by
  intro a b h
  rw [positiveEqualityLaurentOverPoint_eq, positiveEqualityLaurentOverPoint_eq] at h
  have he := finiteGlobalSmoothCoefficientOverPoint_injective hπ data (s + 1) hs K T h
  exact (cancel_mono (g).inv.hom.hom.hom).mp he

end FLT.Mazur.WeierstrassDividedDepth
