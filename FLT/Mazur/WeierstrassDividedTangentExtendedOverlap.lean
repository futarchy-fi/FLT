/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentPartialOverlap
public import FLT.Mazur.WeierstrassDividedTangentSecantOverlap
public import FLT.Mazur.WeierstrassDividedExtendedPartialAddition

/-!
# Tangent compatibility with the existing extended union

The previous partial domain and the secant domain cover the extended union.
Pulling this cover back proves equality with its already glued law.
No assertion that the combined domains cover the full product is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "v" => integralSmoothStructure W
local notation "V" => finiteResolvedExtendedOpen hπ data j hj
local notation "i" => finiteResolvedExtendedInput hπ data j hj

/-- The new resolved formula equals the entire old partial law on every actual overlap. -/
theorem finiteResolvedTangent_extendedOverlap {X : Scheme.{u}}
    (p : X ⟶ (finiteResolvedTangentOutputOpen hπ data j hj).toScheme)
    (q : X ⟶ (V).toScheme)
    (hpq : p ≫ finiteResolvedTangentDomainMap hπ data j hj = q ≫ (V).ι) :
    p ≫ finiteResolvedTangentAddition hπ data j hj =
      q ≫ finiteResolvedExtendedPartialAddition hπ data j hj := by
  apply Scheme.Cover.hom_ext ((openImageUnionCover i).pullback₁ q)
  intro b
  change Bool at b
  let k := pullback.fst q (openImageUnionMap i b)
  let l := pullback.snd q (openImageUnionMap i b)
  have hq : k ≫ q = l ≫ openImageUnionMap i b := pullback.condition
  have he : (k ≫ p) ≫ finiteResolvedTangentDomainMap hπ data j hj = l ≫ i b := by
    rw [Category.assoc, hpq, ← Category.assoc, hq, Category.assoc]
    exact congrArg (l ≫ ·) (openImageUnionMap_fac i b)
  cases b
  · have h := finiteResolvedTangent_partialOverlap hπ data j hj (k ≫ p) l he
    rw [← finiteResolvedExtendedPartialAddition_old hπ data j hj,
      ← Category.assoc, ← hq, Category.assoc] at h
    exact h
  · have h := finiteResolvedTangent_secantOverlap hπ data j hj (k ≫ p) l he
    rw [← finiteResolvedExtendedPartialAddition_secant hπ data j hj,
      ← Category.assoc, ← hq, Category.assoc] at h
    exact h

end FLT.Mazur.WeierstrassDividedDepth
