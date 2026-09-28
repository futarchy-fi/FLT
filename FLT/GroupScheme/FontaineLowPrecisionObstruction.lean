/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineRelativeObstruction
public import FLT.GroupScheme.LocalDvrRealization

/-!
# Low-precision Fontaine obstructions

A ramified Eisenstein presentation admits an approximate root at zero in its
unramified coefficient field. That field has strictly smaller absolute degree,
so Fontaine's property fails at every precision at most one.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- A ramified relative Eisenstein presentation obstructs every Fontaine
precision at most one by specializing its generator to zero. -/
theorem notFontainePropertyOfRamifiedPresentation
    {C : Type} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra ℤ_[3] C] [Module.Finite ℤ_[3] C] [FaithfulSMul ℤ_[3] C]
    [Algebra C (ThreeAdicIntegers L)] [IsScalarTower ℤ_[3] C (ThreeAdicIntegers L)]
    [FaithfulSMul C (ThreeAdicIntegers L)]
    (pb : PowerBasis C (ThreeAdicIntegers L)) (h3 : Irreducible (3 : C))
    (hP : (minpoly C pb.gen).IsEisensteinAt (maximalIdeal C)) (he : 1 < pb.dim)
    (m : ℚ) (hm : m ≤ 1) : ¬ FontaineProperty (ThreeAdicIntegers L) m := by
  let E := FractionRing C
  obtain ⟨instAlgQ, instAlgZ, instTowerQ, instFiniteQ, instAlgInt, instTowerInt, j,
    hdegree, hv⟩ := existsThreeAdicDvrRealization C C E
  let instFiniteC : Module.Finite C (ThreeAdicIntegers L) := pb.finite
  have hL : Module.finrank ℚ_[3] L = Module.finrank ℤ_[3] C * pb.dim := by
    rw [IsFractionRing.finrank_eq ℤ_[3] ℚ_[3] (ThreeAdicIntegers L) L,
      ← Module.finrank_mul_finrank ℤ_[3] C (ThreeAdicIntegers L), pb.finrank]
  have hsmall : Module.finrank ℚ_[3] E < Module.finrank ℚ_[3] L := by
    rw [hdegree, Module.finrank_self, mul_one, hL]
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left he
      (show 0 < Module.finrank ℤ_[3] C from Module.finrank_pos)
  have hE : threeAdicIdealOrder E (Ideal.span {(3 : ThreeAdicIntegers E)}) = 1 := by
    have h := hv (3 : C)
    rw [map_ofNat, IsDiscreteValuationRing.addVal_uniformizer h3,
      threeAdicAddValEqIdealOrder E (3 : ThreeAdicIntegers E) (by
        let instCharZero : CharZero (ThreeAdicIntegers E) := Algebra.charZero_of_charZero ℤ_[3] _
        norm_num)] at h
    exact ENat.natCast_inj.mp h
  have hy : IsDiscreteValuationRing.addVal (ThreeAdicIntegers E)
      (aeval (j 0) (minpoly C pb.gen)) = (1 : ℕ∞) := by
    rw [aeval_algHom_apply, hv]
    simpa [← Polynomial.coeff_zero_eq_eval_zero] using IsDiscreteValuationRing.addVal_uniformizer
      (hP.irreducibleCoeffZero (by rw [pb.natDegree_minpoly]; omega))
  apply notFontainePropertyOfRelativeApproximateRoot L E pb m (j 0)
  · exact threeAdicMemValuationIdealOfAddVal E _ 1 hy m (by simpa [hE] using hm)
  · rintro ⟨i⟩
    exact (not_le_of_gt hsmall)
      (LinearMap.finrank_le_finrank_of_injective (f := i.toLinearMap) i.injective)

end ThreeAdicPlan
