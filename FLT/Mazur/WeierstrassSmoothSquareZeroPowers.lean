/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothSquareZeroKernel
public import FLT.Mazur.KernelPowerTorsionLifting

/-!
# Unit-index powers in the smooth square-zero kernel

Multiplication by a unit acts bijectively on the infinitesimal ideal. The
constructed kernel equivalence therefore gives unique power roots and unique
torsion corrections in the actual smooth Weierstrass group.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (I : Ideal A) (hI : I ^ 2 = ⊥)
  (n : ℕ) (hn : IsUnit (n : A))

include hI hn

/-- The nth-power map on the entire square-zero reduction kernel is bijective. -/
theorem smoothSquareZeroKernel_pow_bijective :
    Function.Bijective (fun z : (smoothSquareZeroReduction W I).ker ↦ z ^ n) := by
  let e := smoothSquareZeroKernelEquiv W I hI
  have hb : Function.Bijective (fun x : I ↦ n • x) := by
    simpa only [Nat.cast_smul_eq_nsmul] using (hn.smul_bijective (β := I))
  constructor
  · intro x y h
    apply e.symm.injective
    have he := congrArg (fun z ↦ (e.symm z).toAdd) h
    simp only [map_pow, toAdd_pow] at he
    exact hb.1 he
  · intro z
    obtain ⟨x, hx⟩ := hb.2 (e.symm z).toAdd
    refine ⟨e (Multiplicative.ofAdd x), e.symm.injective ?_⟩
    change Multiplicative.ofAdd ((e.symm (e (Multiplicative.ofAdd x) ^ n)).toAdd) = _
    rw [map_pow, e.symm_apply_apply, toAdd_pow]
    exact congrArg Multiplicative.ofAdd hx

/-- Every chosen lift of a torsion point has a unique torsion correction. -/
theorem smoothSquareZero_existsUnique_torsion_correction
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralSmoothGroup W).X)
    (hx : smoothSquareZeroReduction W I x ^ n = 1) :
    ∃! y, smoothSquareZeroReduction W I y = smoothSquareZeroReduction W I x ∧ y ^ n = 1 :=
  KernelPowerTorsionLifting.existsUnique_torsion_lift (smoothSquareZeroReduction W I) n
    (smoothSquareZeroKernel_pow_bijective W I hI n hn) x hx

/-- Two unit-index torsion points with the same square-zero reduction coincide. -/
theorem smoothSquareZero_torsion_injective
    (x y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralSmoothGroup W).X)
    (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hxy : squareZeroQuotientTestMap I ≫ x = squareZeroQuotientTestMap I ≫ y) : x = y :=
  KernelPowerTorsionLifting.torsion_lift_unique (smoothSquareZeroReduction W I) n
    (smoothSquareZeroKernel_pow_bijective W I hI n hn).1 hx hy hxy

end FLT.Mazur.WeierstrassIntegralChart
