/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageNodeBranchReconstruction
public import FLT.Mazur.PolygonSmoothingReciprocalScaling
public import FLT.Mazur.PolygonChartScaling

/-!
# Two generators detect preservation of the full original node subalgebra

The two Laurent substitutions act on the product of punctured branches.
They preserve the embedded node precisely when both explicit coordinate
images belong to it. Reconstruction gives the induced map and proves its
uniqueness, on every original function rather than only on generators.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentUnitPoints PolygonChartScaling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R m
local notation "e" => parameter R m
local notation "B" => ChartRing (e)
local notation "L" => (S)[T;T⁻¹]

/-- Apply the full two prescribed substitutions to the two punctured branches. -/
def stageNodeBranchSubstitution (u v : (L)ˣ) : ((L) × (L)) →ₐ[S] ((L) × (L)) :=
  (evalUnit u).prodMap (evalUnit v)

/-- The first original generator has exactly the required coordinate pair. -/
theorem stageNodeBranchSubstitution_left (u v : (L)ˣ) :
    stageNodeBranchSubstitution R m u v (stageNodeBranchPair R m (leftCoordinate (e))) =
      stageNodeBranchLeftImage R m u v := by
  apply Prod.ext
  · change evalUnit u (leftLaurentMap (e) (leftCoordinate (e))) = u.val
    rw [leftLaurentMap_left, evalUnit_T, zpow_one]
  · change evalUnit v (leftLaurentMap (e) (branchSwapMap (e) (leftCoordinate (e)))) = _
    rw [branchSwapMap_left, leftLaurentMap_right, map_mul, evalUnit_C,
      evalUnit_T, zpow_neg_one]
    rfl

/-- The second original generator has exactly the other required coordinate pair. -/
theorem stageNodeBranchSubstitution_right (u v : (L)ˣ) :
    stageNodeBranchSubstitution R m u v (stageNodeBranchPair R m (rightCoordinate (e))) =
      stageNodeBranchRightImage R m u v := by
  apply Prod.ext
  · change evalUnit u (leftLaurentMap (e) (rightCoordinate (e))) = _
    rw [leftLaurentMap_right, map_mul, evalUnit_C, evalUnit_T, zpow_neg_one]
    rfl
  · change evalUnit v (leftLaurentMap (e) (branchSwapMap (e) (rightCoordinate (e)))) = v.val
    rw [branchSwapMap_right, leftLaurentMap_left, evalUnit_T, zpow_one]

/-- The reconstructed node map induces the entire original pair substitution. -/
theorem stageNodeBranchReconstruct_pair (u v : (L)ˣ)
    (hx : stageNodeBranchLeftImage R m u v ∈ stageNodeBranchSubalgebra R m)
    (hy : stageNodeBranchRightImage R m u v ∈ stageNodeBranchSubalgebra R m) (z : B) :
    stageNodeBranchPair R m (stageNodeBranchReconstruct R m u v hx hy z) =
      stageNodeBranchSubstitution R m u v (stageNodeBranchPair R m z) := by
  apply Prod.ext
  · exact AlgHom.congr_fun (stageNodeBranchReconstruct_leftLaurent R m u v hx hy) z
  · exact AlgHom.congr_fun (stageNodeBranchReconstruct_rightLaurent R m u v hx hy) z

/-- Two explicit original-coordinate membership tests detect preservation of all functions. -/
theorem stageNodeBranchSubstitution_preserves_iff (u v : (L)ˣ) :
    (∀ p ∈ stageNodeBranchSubalgebra R m,
      stageNodeBranchSubstitution R m u v p ∈ stageNodeBranchSubalgebra R m) ↔
    stageNodeBranchLeftImage R m u v ∈ stageNodeBranchSubalgebra R m ∧
      stageNodeBranchRightImage R m u v ∈ stageNodeBranchSubalgebra R m := by
  constructor
  · intro hp
    constructor
    · rw [← stageNodeBranchSubstitution_left R m u v]
      exact hp _ ⟨leftCoordinate (e), rfl⟩
    · rw [← stageNodeBranchSubstitution_right R m u v]
      exact hp _ ⟨rightCoordinate (e), rfl⟩
  · rintro ⟨hx, hy⟩ p ⟨z, rfl⟩
    exact ⟨stageNodeBranchReconstruct R m u v hx hy z,
      stageNodeBranchReconstruct_pair R m u v hx hy z⟩

/-- There is exactly one original-node map inducing the prescribed full branch substitution. -/
theorem stageNodeBranchReconstruct_unique (u v : (L)ˣ)
    (hx : stageNodeBranchLeftImage R m u v ∈ stageNodeBranchSubalgebra R m)
    (hy : stageNodeBranchRightImage R m u v ∈ stageNodeBranchSubalgebra R m)
    (f : (B) →ₐ[S] (B))
    (hf : ∀ z, stageNodeBranchPair R m (f z) =
      stageNodeBranchSubstitution R m u v (stageNodeBranchPair R m z)) :
    f = stageNodeBranchReconstruct R m u v hx hy := by
  apply AlgHom.ext
  intro z
  apply stageNodeBranchPair_injective R m
  exact (hf z).trans (stageNodeBranchReconstruct_pair R m u v hx hy z).symm

/-- Full reciprocal node scaling has exactly the two prescribed Laurent scaling restrictions. -/
theorem stageNodeBranchPair_scaling (a : (S)ˣ) (z : B) :
    stageNodeBranchSubstitution R m (coordinateUnit a) (coordinateUnit a⁻¹)
        (stageNodeBranchPair R m z) =
      stageNodeBranchPair R m (reciprocalScale (e) a z) := by
  have he : (stageNodeBranchSubstitution R m (coordinateUnit a) (coordinateUnit a⁻¹)).comp
      (stageNodeBranchPair R m) = (stageNodeBranchPair R m).comp (reciprocalScale (e) a) := by
    apply chartRing_hom_ext (e)
    · change stageNodeBranchSubstitution R m _ _ (stageNodeBranchPair R m (leftCoordinate (e))) = _
      rw [stageNodeBranchSubstitution_left]
      apply Prod.ext
      · simp only [stageNodeBranchLeftImage, stageNodeBranchPair, AlgHom.comp_apply,
          AlgHom.prod_apply, reciprocalScale_left, map_mul, AlgHom.commutes,
          leftLaurentMap_left, coordinateUnit]
        rfl
      · change C (e) * (coordinateUnit a⁻¹)⁻¹.val =
          leftLaurentMap (e) (branchSwapMap (e) (reciprocalScale (e) a (leftCoordinate (e))))
        simp only [reciprocalScale_left, map_mul, AlgHom.commutes, branchSwapMap_left,
          leftLaurentMap_right, ← C_eq_algebraMap]
        change C (e) * (C (a⁻¹)⁻¹.val * T (-1)) = C a.val * (C (e) * T (-1))
        rw [inv_inv]
        ring
    · change stageNodeBranchSubstitution R m _ _ (stageNodeBranchPair R m (rightCoordinate (e))) = _
      rw [stageNodeBranchSubstitution_right]
      apply Prod.ext
      · change C (e) * (coordinateUnit a)⁻¹.val =
          leftLaurentMap (e) (reciprocalScale (e) a (rightCoordinate (e)))
        simp only [reciprocalScale_right, map_mul, AlgHom.commutes,
          leftLaurentMap_right, ← C_eq_algebraMap]
        change C (e) * (C a⁻¹.val * T (-1)) = C a⁻¹.val * (C (e) * T (-1))
        ring
      · change (coordinateUnit a⁻¹).val =
          leftLaurentMap (e) (branchSwapMap (e) (reciprocalScale (e) a (rightCoordinate (e))))
        rw [reciprocalScale_right, map_mul, AlgHom.commutes, branchSwapMap_right,
          map_mul, AlgHom.commutes, leftLaurentMap_left]
        rfl
  exact AlgHom.congr_fun he z

end FLT.Mazur.PolygonInfinitesimalStages
