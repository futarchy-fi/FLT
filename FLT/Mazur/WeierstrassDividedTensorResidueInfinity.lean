/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTensorInfinityPreimage
public import FLT.Mazur.WeierstrassDividedInfinitySmoothCompatibility

/-!
# The positive-depth terminal tensor chart misses infinity

The original affine Y contracts with its uniformizer power. This vanishes
on the residue fiber, separating the entire terminal chart from identity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "C" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S
local notation "g" => globalDividedTensorChart hπ data S j hj
local notation "i" => finiteInfinityTensorChart hπ data S j hj

/-- The full terminal tensor chart has empty infinity preimage at positive residue depth. -/
theorem globalDividedTensor_residue_infinity_preimage (hp : algebraMap R S π = 0)
    (hk : 0 < start + j) : g ⁻¹' Set.range i = ∅ := by
  rw [globalDividedTensor_infinity_preimage]
  let f : C →ₐ[R] T := Algebra.TensorProduct.includeRight
  ext z
  change (f
    ((WeierstrassDilatation.fromOriginal W (π ^ (start + j))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
      (Data.factor6 d)) (WeierstrassIntegralChart.coord W 2 1))) ∉ z.asIdeal ↔ False
  have hz : algebraMap R T (π ^ (start + j)) = 0 := by
    rw [IsScalarTower.algebraMap_apply R S T, map_pow, hp,
      zero_pow (Nat.ne_of_gt hk), map_zero]
  rw [WeierstrassDilatation.fromOriginal_y, map_mul, AlgHom.commutes, hz, zero_mul]
  exact iff_false_intro (not_not_intro z.asIdeal.zero_mem)

/-- The entire positive-depth divided tensor chart is disjoint from the infinity tensor chart. -/
theorem globalDividedTensor_residue_infinity_disjoint (hp : algebraMap R S π = 0)
    (hk : 0 < start + j) : Disjoint (Set.range g) (Set.range i) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ hx
  exact (Set.ext_iff.mp (globalDividedTensor_residue_infinity_preimage
    hπ data S j hj hp hk) x).mp hx

variable {K : Type u} [Field K] (A : ValuationSubring K)
  {U : WeierstrassCurve A} {ϖ : A} {depth : ℕ} (D : SplitNodeDepth U ϖ depth)

/-- The complete actual terminal member misses the original identity torus at positive stage. -/
theorem resolvedTerminal_identity_disjoint (hk : 0 < depth / 2) :
    Disjoint (Set.range (globalDividedTensorChart (SplitNodeDepth.uniformizer_ne_zero D)
      (splitResolutionData A D) (ResidueField A) (depth / 2) (le_refl _)))
      (Set.range (resolvedIdentityChart A D)) := by
  rw [resolvedIdentityChart_range_infinity]
  apply globalDividedTensor_residue_infinity_disjoint
  · exact (residue_eq_zero_iff ϖ).mpr
      (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ)
  · omega

end FLT.Mazur.WeierstrassDividedDepth
