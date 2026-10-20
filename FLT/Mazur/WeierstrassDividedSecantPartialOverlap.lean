/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantRightOverlap
public import FLT.Mazur.WeierstrassDividedResolvedPartialAddition

/-!
# Equality on the overlap with the whole previous partial addition

The two original-factor charts cover the old domain. Pulling this cover
back to an arbitrary overlap proves equality with its already glued law.
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
local notation "V" => finiteResolvedOriginalFactorOpen hπ data j hj
local notation "i" => finiteResolvedInput hπ data j hj

/-- Both original input orders have the same resolved secant output on their overlap. -/
theorem finiteResolvedSecant_orderOverlap {X : Scheme.{u}} (b : Bool)
    (p : X ⟶ (finiteResolvedSecantOutputOpen hπ data j hj).toScheme)
    (q : X ⟶ pullback v t) (hpq : p ≫ finiteResolvedSecantDomainMap hπ data j hj = q ≫ i b) :
    p ≫ finiteResolvedSecantAddition hπ data j hj =
      q ≫ finiteGlobalSmoothAction hπ data j hj := by
  cases b
  · exact finiteResolvedSecant_leftOverlap hπ data j hj p q hpq
  · exact finiteResolvedSecant_rightOverlap hπ data j hj p q hpq

/-- The new resolved formula equals the entire old partial law on every actual overlap. -/
theorem finiteResolvedSecant_partialOverlap {X : Scheme.{u}}
    (p : X ⟶ (finiteResolvedSecantOutputOpen hπ data j hj).toScheme)
    (q : X ⟶ (V).toScheme)
    (hpq : p ≫ finiteResolvedSecantDomainMap hπ data j hj = q ≫ (V).ι) :
    p ≫ finiteResolvedSecantAddition hπ data j hj =
      q ≫ finiteResolvedPartialAddition hπ data j hj := by
  apply Scheme.Cover.hom_ext ((openImageUnionCover i).pullback₁ q)
  intro b
  change Bool at b
  let k := pullback.fst q (openImageUnionMap i b)
  let l := pullback.snd q (openImageUnionMap i b)
  have hq : k ≫ q = l ≫ openImageUnionMap i b := pullback.condition
  have he : (k ≫ p) ≫ finiteResolvedSecantDomainMap hπ data j hj = l ≫ i b := by
    rw [Category.assoc, hpq, ← Category.assoc, hq, Category.assoc]
    exact congrArg (l ≫ ·) (openImageUnionMap_fac i b)
  have h := finiteResolvedSecant_orderOverlap hπ data j hj b (k ≫ p) l he
  rw [← finiteResolvedPartialAddition_chart hπ data j hj b,
    ← Category.assoc, ← hq, Category.assoc] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
