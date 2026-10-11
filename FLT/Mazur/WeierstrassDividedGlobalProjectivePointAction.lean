/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalPointSubgroups
public import FLT.Mazur.WeierstrassSmoothProjectiveGroup

/-!
# Original projective point groups act faithfully at every finite depth

The classical addition law gives actual translations on every field-valued
point of the finite model. This requires no split reduction hypothesis.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

variable (j : ℕ) (hj : j ≤ n)

variable (K : Type u) [Field K] [Algebra R K]
local notation "T" => Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)))
local notation "X" => T ⟶ Over.mk (finiteGlobalStructure hπ data j hj)

/-- Classical projective points act by their original scheme maps and addition law. -/
def finiteGlobalProjectivePointPermutation :
    (W.map (algebraMap R K)).toProjective.Point →+ Additive (Equiv.Perm X) :=
  (finiteGlobalPointPermutation hπ data j hj T).toAdditive.comp
    (smoothProjectivePointAddEquiv (K := K) W).toAddMonoidHom

/-- Every classical point keeps its original translation morphism on all modified points. -/
theorem finiteGlobalProjectivePointPermutation_apply
    (P : (W.map (algebraMap R K)).toProjective.Point) (x : X) :
    ((finiteGlobalProjectivePointPermutation hπ data j hj K P).toMul x).left =
      finiteGlobalPointAction hπ data j hj (projectiveToSmooth W P) x.left
        (by exact (projectiveToSmoothOver W P).w.trans x.w.symm) := rfl

/-- Distinct classical points induce distinct translations of the actual finite model. -/
theorem finiteGlobalProjectivePointPermutation_injective :
    Function.Injective (finiteGlobalProjectivePointPermutation hπ data j hj K) := by
  intro P Q h
  apply (smoothProjectivePointAddEquiv (K := K) W).injective
  exact finiteGlobalPointPermutation_injective hπ data j hj T h

/-- Original integer torsion is detected exactly by the constructed translations. -/
theorem finiteGlobalProjectivePointPermutation_torsion_iff (m : ℤ)
    (P : (W.map (algebraMap R K)).toProjective.Point) :
    m • finiteGlobalProjectivePointPermutation hπ data j hj K P = 0 ↔ m • P = 0 := by
  rw [← map_zsmul, ← map_zero (finiteGlobalProjectivePointPermutation hπ data j hj K)]
  exact (finiteGlobalProjectivePointPermutation_injective hπ data j hj K).eq_iff

/-- Every classical point subgroup is isomorphic to its actual translation image. -/
def finiteGlobalProjectiveSubgroupEquiv
    (H : AddSubgroup (W.map (algebraMap R K)).toProjective.Point) :
    H ≃+ H.map (finiteGlobalProjectivePointPermutation hπ data j hj K) :=
  H.equivMapOfInjective (finiteGlobalProjectivePointPermutation hπ data j hj K)
    (finiteGlobalProjectivePointPermutation_injective hπ data j hj K)

/-- Every original finite subgroup retains its exact order at every finite depth. -/
theorem finiteGlobalProjectiveSubgroup_card
    (H : AddSubgroup (W.map (algebraMap R K)).toProjective.Point) :
    Nat.card (H.map (finiteGlobalProjectivePointPermutation hπ data j hj K)) = Nat.card H :=
  Nat.card_congr (finiteGlobalProjectiveSubgroupEquiv hπ data j hj K H).toEquiv.symm

end FLT.Mazur.WeierstrassDividedDepth
