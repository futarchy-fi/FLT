/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSmoothReductionAddition

/-!
# The actual smooth-reduction subgroup and its kernel

For any integral Weierstrass equation over a valuation subring, `ellipticE0`
is the subgroup of generic points with smooth reduction. Its reduction map is
an additive homomorphism to the actual smooth special cubic. `ellipticE1` is
the infinity fiber in the generic group, and is identified with that kernel.
These constructions do not assert a Néron-model comparison or a torsion bound.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Generic points with smooth reduction form the subgroup E₀. -/
def ellipticE0 : AddSubgroup (W.map (algebraMap A K)).toProjective.Point where
  carrier := SmoothReduction A W
  zero_mem' := smoothReduction_zero A W
  add_mem' := fun hp hq => hp.add A W hq
  neg_mem' := fun hp => hp.neg A W

/-- The actual reduction homomorphism on E₀, including at bad reduction. -/
noncomputable def smoothReductionHom :
    ellipticE0 A W →+ (W.map (residue A)).toProjective.Point where
  toFun := smoothReductionPoint A W
  map_zero' := Point.ext (projectiveReduction_zero A W)
  map_add' := smoothReductionPoint_add A W

/-- The infinity fiber is closed under addition. -/
theorem InfinityReduction.add {P Q : (W.map (algebraMap A K)).toProjective.Point}
    (hp : InfinityReduction A W P) (hq : InfinityReduction A W Q) :
    InfinityReduction A W (P + Q) := by
  let p : ellipticE0 A W := ⟨P, hp.smooth A W⟩
  let q : ellipticE0 A W := ⟨Q, hq.smooth A W⟩
  have hp0 : smoothReductionHom A W p = 0 :=
    (smoothReductionPoint_eq_zero_iff A W p).mpr hp
  have hq0 : smoothReductionHom A W q = 0 :=
    (smoothReductionPoint_eq_zero_iff A W q).mpr hq
  apply (smoothReductionPoint_eq_zero_iff A W (p + q)).mp
  change smoothReductionHom A W (p + q) = 0
  rw [map_add, hp0, hq0, add_zero]

/-- The infinity fiber is the subgroup E₁ of actual generic points. -/
def ellipticE1 : AddSubgroup (W.map (algebraMap A K)).toProjective.Point where
  carrier := InfinityReduction A W
  zero_mem' := infinityReduction_zero A W
  add_mem' := fun hp hq => hp.add A W hq
  neg_mem' := fun hp => hp.neg A W

/-- Every E₁ point lies in E₀. -/
theorem ellipticE1_le_ellipticE0 : ellipticE1 A W ≤ ellipticE0 A W :=
  fun _ hp => hp.smooth A W

/-- On E₀, membership in E₁ is exactly membership in the reduction kernel. -/
theorem mem_smoothReductionHom_ker_iff (P : ellipticE0 A W) :
    P ∈ (smoothReductionHom A W).ker ↔ P.val ∈ ellipticE1 A W :=
  smoothReductionPoint_eq_zero_iff A W P

/-- The kernel as a subgroup of E₀ is the inverse image of E₁ under inclusion. -/
theorem smoothReductionHom_ker :
    (smoothReductionHom A W).ker = (ellipticE1 A W).comap (ellipticE0 A W).subtype := by
  ext P
  exact mem_smoothReductionHom_ker_iff A W P

/-- Each E₁ point has integral local coordinates in the maximal ideal. -/
theorem ellipticE1_exists_parameters (P : ellipticE1 A W)
    (v : PrimitiveLift A P.val.point) :
    ∃ t s : A, (t : K) = -(v.coords 0 : K) / (v.coords 1 : K) ∧
      (s : K) = -(v.coords 2 : K) / (v.coords 1 : K) ∧
      t ∈ maximalIdeal A ∧ s ∈ maximalIdeal A ∧
      s = t ^ 3 + W.a₁ * t * s + W.a₂ * t ^ 2 * s + W.a₃ * s ^ 2 +
        W.a₄ * t * s ^ 2 + W.a₆ * s ^ 3 :=
  exists_infinity_parameters A W v P.property

end FLT.Mazur
