/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticStarDeepCoordinates

/-!
# The normalized type II* rational component calculation

At depths (1,2,3,4,5), every point outside E₀ would have coordinates
(π²x,π³y). Its equation would put a₆ in m⁶. Thus exact depth five of a₆
excludes all such points and makes the actual component quotient trivial.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- The deep point equation forces depth six of the constant coefficient. -/
theorem a6_mem_sixth_of_starDeep_equation {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (I : Ideal R) {x y : R}
    (he : W.toAffine.Equation x y) (h1 : W.a₁ ∈ I) (h2 : W.a₂ ∈ I ^ 2)
    (h3 : W.a₃ ∈ I ^ 3) (h4 : W.a₄ ∈ I ^ 4) (hx : x ∈ I ^ 2) (hy : y ∈ I ^ 3) :
    W.a₆ ∈ I ^ 6 := by
  have hxy : W.a₁ * x ∈ I ^ 3 := by
    simpa only [pow_succ'] using Ideal.mul_mem_mul h1 hx
  have hx2 : x ^ 2 ∈ I ^ 4 := by simpa only [← pow_mul] using Ideal.pow_mem_pow hx 2
  have hy2 : y ^ 2 ∈ I ^ 6 := by simpa only [← pow_mul] using Ideal.pow_mem_pow hy 2
  have hx3 : x ^ 3 ∈ I ^ 6 := by simpa only [← pow_mul] using Ideal.pow_mem_pow hx 3
  have ht : W.a₁ * x * y ∈ I ^ 6 := by
    simpa only [← pow_add] using Ideal.mul_mem_mul hxy hy
  have h3y : W.a₃ * y ∈ I ^ 6 := by
    simpa only [← pow_add] using Ideal.mul_mem_mul h3 hy
  have h2x : W.a₂ * x ^ 2 ∈ I ^ 6 := by
    simpa only [← pow_add] using Ideal.mul_mem_mul h2 hx2
  have h4x : W.a₄ * x ∈ I ^ 6 := by
    simpa only [← pow_add] using Ideal.mul_mem_mul h4 hx
  have heq : W.a₆ = y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      x ^ 3 - W.a₂ * x ^ 2 - W.a₄ * x := by
    linear_combination -(Affine.equation_iff _ _).mp he
  rw [heq]
  exact (I ^ 6).sub_mem ((I ^ 6).sub_mem ((I ^ 6).sub_mem
    ((I ^ 6).add_mem ((I ^ 6).add_mem hy2 ht) h3y) hx3) h2x) h4x

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  {π : A} (hπ : π ≠ 0) (hgen : maximalIdeal A = Ideal.span {π})
  (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A ^ 2)
  (h3 : W.a₃ ∈ maximalIdeal A ^ 3) (h4 : W.a₄ ∈ maximalIdeal A ^ 4)
  (h6 : W.a₆ ∈ maximalIdeal A ^ 5) (h6' : W.a₆ ∉ maximalIdeal A ^ 6)

include hπ hgen h1 h2 h3 h4 h6 h6'

/-- Every generic point reduces smoothly under the normalized type II* tests. -/
theorem smoothReduction_of_normalizedTypeIIStar
    (P : (W.map (algebraMap A K)).toProjective.Point) : SmoothReduction A W P := by
  by_contra hP
  obtain ⟨v⟩ := exists_starDeepCoordinates A W hπ hgen h1 h2 h3
    (Ideal.pow_le_pow_right (by decide : 3 ≤ 4) h4) h6 P hP
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  apply h6'
  exact a6_mem_sixth_of_starDeep_equation W _ v.equation h1 h2 h3 h4
    ((maximalIdeal A ^ 2).mul_mem_right _ (Ideal.pow_mem_pow hπm 2))
    ((maximalIdeal A ^ 3).mul_mem_right _ (Ideal.pow_mem_pow hπm 3))

/-- The normalized type II* rational component quotient is trivial. -/
theorem ellipticComponent_subsingleton_of_normalizedTypeIIStar :
    Subsingleton (EllipticComponentQuotient A W) := by
  have hz (c : EllipticComponentQuotient A W) : c = 0 := by
    obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
    exact (ellipticComponentHom_eq_zero A W P).mpr
      (smoothReduction_of_normalizedTypeIIStar A W hπ hgen h1 h2 h3 h4 h6 h6' P)
  exact ⟨fun c d => (hz c).trans (hz d).symm⟩

end FLT.Mazur
