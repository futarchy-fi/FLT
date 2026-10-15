/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeBranchReduction
public import FLT.Mazur.PolygonFirstNodeScaledBoundary
public import FLT.Mazur.PolygonFirstNodeAutomorphism

/-!
# Full node automorphisms from preserved branch coordinates

The reconstructed map is automatically invertible when its closed reduction
is reciprocal scaling. Swapping the two branch factors retains the original
node subalgebra and constructs the corresponding opposite-node map.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)

/-- Interchanging branch factors retains the original node embedding. -/
theorem firstNodeBranchPair_swap (z : B) :
    firstNodeBranchPair R (branchSwapMap (e) z) = (firstNodeBranchPair R z).swap := by
  apply Prod.ext
  · rfl
  · change leftLaurentMap (e) (branchSwapMap (e) (branchSwapMap (e) z)) = _
    have he := AlgHom.congr_fun (branchSwapMap_comp (e)) z
    exact congrArg (leftLaurentMap (e)) he

/-- The original coordinate subalgebra is invariant under interchanging its two branches. -/
theorem firstNodeBranchSubalgebra_swap (p : (S)[T;T⁻¹] × (S)[T;T⁻¹])
    (hp : p ∈ firstNodeBranchSubalgebra R) : p.swap ∈ firstNodeBranchSubalgebra R := by
  obtain ⟨z, rfl⟩ := hp
  exact ⟨branchSwapMap (e) z, firstNodeBranchPair_swap R z⟩

/-- The original second coordinate supplies the opposite first coordinate. -/
theorem firstNodeBranchLeftImage_swap (u v : (S)[T;T⁻¹]ˣ)
    (hy : firstNodeBranchRightImage R u v ∈ firstNodeBranchSubalgebra R) :
    firstNodeBranchLeftImage R v u ∈ firstNodeBranchSubalgebra R :=
  firstNodeBranchSubalgebra_swap R _ hy

/-- The original first coordinate supplies the opposite second coordinate. -/
theorem firstNodeBranchRightImage_swap (u v : (S)[T;T⁻¹]ˣ)
    (hx : firstNodeBranchLeftImage R u v ∈ firstNodeBranchSubalgebra R) :
    firstNodeBranchRightImage R v u ∈ firstNodeBranchSubalgebra R :=
  firstNodeBranchSubalgebra_swap R _ hx

/-- Any scaling-reducing node map is invertible, without an inverse preservation hypothesis. -/
def firstNodeScalingEndomorphismEquiv (a : (S)ˣ) (f : (B) →ₐ[S] (B))
    (hf : ∀ z, firstNodeReduction R (f z) =
      firstNodeReduction R (reciprocalScale (e) a z)) : (B) ≃ₐ[S] (B) :=
  (reciprocalScaleEquiv (e) a).trans
    (firstNodeEndomorphismEquiv R (firstNodeScaleNormalize R a f)
      (firstNodeScaleNormalize_reduction R a f hf))

/-- Promoting the map to an automorphism retains its value on every original function. -/
theorem firstNodeScalingEndomorphismEquiv_apply (a : (S)ˣ) (f : (B) →ₐ[S] (B))
    (hf : ∀ z, firstNodeReduction R (f z) =
      firstNodeReduction R (reciprocalScale (e) a z)) (z : B) :
    firstNodeScalingEndomorphismEquiv R a f hf z = f z := by
  change f (reciprocalScale (e) a⁻¹ (reciprocalScale (e) a z)) = f z
  have he := AlgHom.congr_fun (reciprocalScale_mul (e) a⁻¹ a) z
  rw [inv_mul_cancel, reciprocalScale_one] at he
  exact congrArg f he.symm

variable (u v : ((Ring R 1)[T;T⁻¹])ˣ)
  (hx : firstNodeBranchLeftImage R u v ∈ firstNodeBranchSubalgebra R)
  (hy : firstNodeBranchRightImage R u v ∈ firstNodeBranchSubalgebra R)
  (a : (Ring R 1)ˣ)
  (hu : coeffMap (reduction R 1).toRingHom u.val =
    C (reduction R 1 a.val) * T 1)
  (hv : coeffMap (reduction R 1).toRingHom v.val =
    C (reduction R 1 a⁻¹.val) * T 1)

/-- Two preserved original coordinates construct a full node automorphism. -/
def firstNodeBranchAutomorphism : (B) ≃ₐ[S] (B) :=
  firstNodeScalingEndomorphismEquiv R a (firstNodeBranchReconstruct R u v hx hy)
    (firstNodeBranchReconstruct_reduction R u v hx hy a hu hv)

/-- This automorphism retains exactly the reconstructed original map. -/
theorem firstNodeBranchAutomorphism_apply (z : B) :
    firstNodeBranchAutomorphism R u v hx hy a hu hv z =
      firstNodeBranchReconstruct R u v hx hy z :=
  firstNodeScalingEndomorphismEquiv_apply R a _ _ z

end FLT.Mazur.PolygonInfinitesimalStages
