/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeBranchReconstruction

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
open PolygonSmoothing LaurentPolynomial LaurentUnitPoints
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)
local notation "L" => (S)[T;T⁻¹]

/-- Apply the full two prescribed substitutions to the two punctured branches. -/
def firstNodeBranchSubstitution (u v : (L)ˣ) : ((L) × (L)) →ₐ[S] ((L) × (L)) :=
  (evalUnit u).prodMap (evalUnit v)

/-- The first original generator has exactly the required coordinate pair. -/
theorem firstNodeBranchSubstitution_left (u v : (L)ˣ) :
    firstNodeBranchSubstitution R u v (firstNodeBranchPair R (leftCoordinate (e))) =
      firstNodeBranchLeftImage R u v := by
  apply Prod.ext
  · change evalUnit u (leftLaurentMap (e) (leftCoordinate (e))) = u.val
    rw [leftLaurentMap_left, evalUnit_T, zpow_one]
  · change evalUnit v (leftLaurentMap (e) (branchSwapMap (e) (leftCoordinate (e)))) = _
    rw [branchSwapMap_left, leftLaurentMap_right, map_mul, evalUnit_C,
      evalUnit_T, zpow_neg_one]
    rfl

/-- The second original generator has exactly the other required coordinate pair. -/
theorem firstNodeBranchSubstitution_right (u v : (L)ˣ) :
    firstNodeBranchSubstitution R u v (firstNodeBranchPair R (rightCoordinate (e))) =
      firstNodeBranchRightImage R u v := by
  apply Prod.ext
  · change evalUnit u (leftLaurentMap (e) (rightCoordinate (e))) = _
    rw [leftLaurentMap_right, map_mul, evalUnit_C, evalUnit_T, zpow_neg_one]
    rfl
  · change evalUnit v (leftLaurentMap (e) (branchSwapMap (e) (rightCoordinate (e)))) = v.val
    rw [branchSwapMap_right, leftLaurentMap_left, evalUnit_T, zpow_one]

/-- The reconstructed node map induces the entire original pair substitution. -/
theorem firstNodeBranchReconstruct_pair (u v : (L)ˣ)
    (hx : firstNodeBranchLeftImage R u v ∈ firstNodeBranchSubalgebra R)
    (hy : firstNodeBranchRightImage R u v ∈ firstNodeBranchSubalgebra R) (z : B) :
    firstNodeBranchPair R (firstNodeBranchReconstruct R u v hx hy z) =
      firstNodeBranchSubstitution R u v (firstNodeBranchPair R z) := by
  apply Prod.ext
  · exact AlgHom.congr_fun (firstNodeBranchReconstruct_leftLaurent R u v hx hy) z
  · exact AlgHom.congr_fun (firstNodeBranchReconstruct_rightLaurent R u v hx hy) z

/-- Two explicit original-coordinate membership tests detect preservation of all functions. -/
theorem firstNodeBranchSubstitution_preserves_iff (u v : (L)ˣ) :
    (∀ p ∈ firstNodeBranchSubalgebra R,
      firstNodeBranchSubstitution R u v p ∈ firstNodeBranchSubalgebra R) ↔
    firstNodeBranchLeftImage R u v ∈ firstNodeBranchSubalgebra R ∧
      firstNodeBranchRightImage R u v ∈ firstNodeBranchSubalgebra R := by
  constructor
  · intro hp
    constructor
    · rw [← firstNodeBranchSubstitution_left R u v]
      exact hp _ ⟨leftCoordinate (e), rfl⟩
    · rw [← firstNodeBranchSubstitution_right R u v]
      exact hp _ ⟨rightCoordinate (e), rfl⟩
  · rintro ⟨hx, hy⟩ p ⟨z, rfl⟩
    exact ⟨firstNodeBranchReconstruct R u v hx hy z,
      firstNodeBranchReconstruct_pair R u v hx hy z⟩

/-- There is exactly one original-node map inducing the prescribed full branch substitution. -/
theorem firstNodeBranchReconstruct_unique (u v : (L)ˣ)
    (hx : firstNodeBranchLeftImage R u v ∈ firstNodeBranchSubalgebra R)
    (hy : firstNodeBranchRightImage R u v ∈ firstNodeBranchSubalgebra R)
    (f : (B) →ₐ[S] (B))
    (hf : ∀ z, firstNodeBranchPair R (f z) =
      firstNodeBranchSubstitution R u v (firstNodeBranchPair R z)) :
    f = firstNodeBranchReconstruct R u v hx hy := by
  apply AlgHom.ext
  intro z
  apply firstNodeBranchPair_injective R
  exact (hf z).trans (firstNodeBranchReconstruct_pair R u v hx hy z).symm

end FLT.Mazur.PolygonInfinitesimalStages
