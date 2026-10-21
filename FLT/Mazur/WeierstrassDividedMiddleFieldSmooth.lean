/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedHorizontalSmooth
public import FLT.Mazur.WeierstrassDividedFiniteSmoothInput
public import FLT.Mazur.WeierstrassDividedUnequalDepthMiddleCoverage

/-!
# Every field point at the exact middle depth is relatively smooth

The nonzero terminal constant excludes the simultaneous vanishing of both
partials. This includes zero abscissae and zero vertical derivatives in
arbitrary characteristic, without assuming a puncture or a branch choice.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Field K] [Algebra R K] {W : WeierstrassCurve R} {π : R} {l m : ℕ}
  (D : SplitNodeDepth W π m) (e : Data W π l)
  (hl : 0 < l) (hm : 2 * l = m) (hπ0 : algebraMap R K π = 0)
  (a : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] K)

include D hl hm hπ0
/-- The horizontal partial is nonzero at every middle-depth field point. -/
theorem middleFieldPoint_horizontal :
    a (dividedPartial W (π ^ l) e.b3 e.b4 e.b6 0) ≠ 0 := by
  have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R K b = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, rfl⟩ := hb
    rw [map_mul, hπ0, zero_mul]
  have hs : algebraMap R K (π ^ l) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have hlin := divided_linear_deep_mem D e (by omega : l ≤ m + 1)
  have h4 := van e.b4 (Ideal.pow_le_self (by omega) hlin.2)
  have h2 := van W.a₂ D.a₂_mem
  have h6 := ((unequalDepthMiddle_constant_unit D e hm).map (algebraMap R K)).ne_zero
  have ha := (D.a₁_unit.map (algebraMap R K)).ne_zero
  by_cases hy : a (y W (π ^ l) e.b3 e.b4 e.b6) = 0
  · have he := equation_map W (π ^ l) e.b3 e.b4 e.b6 a
    simp only [hy, hs, h2, h4, zero_mul, mul_zero, zero_add, add_zero,
      zero_pow (by decide : 2 ≠ 0)] at he
    exact False.elim (h6 he.symm)
  · simp only [map_pow] at hs
    simpa only [dividedPartial_horizontal, map_sub, map_mul, map_add, map_pow,
      map_ofNat, AlgHom.commutes, hs, h2, h4, mul_zero, zero_mul, zero_add, add_zero, sub_zero]
      using mul_ne_zero ha hy

/-- Every middle-depth field point lies in the original divided relative smooth locus. -/
theorem middleFieldPoint_range_smooth :
    Set.range (Spec.map (CommRingCat.ofHom a.toRingHom)) ⊆
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (Coordinate W (π ^ l) e.b3 e.b4 e.b6)))).smoothLocus := by
  exact dividedPartialUnitPoint_range_smooth W (π ^ l) e.b3 e.b4 e.b6 a 0
    (isUnit_iff_ne_zero.mpr (middleFieldPoint_horizontal D e hl hm hπ0 a))

variable [IsBezout R] [IsNoetherianRing R] {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : l ≤ n)

/-- The whole middle-depth field point is smooth in its unchanged finite model. -/
theorem finiteMiddleFieldPoint_range_smooth
    (b : Coordinate W (π ^ (0 + l))
      (data ⟨l, Nat.lt_succ_of_le hj⟩).b3 (data ⟨l, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨l, Nat.lt_succ_of_le hj⟩).b6 →ₐ[R] K) :
    Set.range (Spec.map (CommRingCat.ofHom b.toRingHom) ≫
      finiteSecantDividedChart D.uniformizer_ne_zero data l hj) ⊆
        (finiteGlobalStructure D.uniformizer_ne_zero data l hj).smoothLocus := by
  rintro _ ⟨z, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq
    (finiteSecantDividedChart D.uniformizer_ne_zero data l hj)
    (finiteGlobalStructure D.uniformizer_ne_zero data l hj)
  simp only [finiteSecantDividedChart_structure] at h
  exact h.ge (middleFieldPoint_range_smooth D _ (by omega) (by omega) hπ0 b ⟨z, rfl⟩)

end FLT.Mazur.WeierstrassDividedDepth
