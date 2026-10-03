/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormalizedOrder
public import FLT.GroupScheme.KummerUnitClass

/-!
# Order modulo powers and the independent unit subgroup

Normalized order modulo n descends to Kummer power classes. Its kernel is
exactly the image of valuation-ring units. Thus a non-unit power class has
a nonzero order-modulo-n coordinate, before invoking any reciprocity map.
-/

@[expose] public section

namespace LocalClassFieldTheory

open ValuativeRel KummerTheory

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ)

/-- Normalized order reduced modulo n. -/
noncomputable def orderMod : Kˣ →* Multiplicative (ZMod n) :=
  (Int.castAddHom (ZMod n)).toMultiplicative.comp (normalizedOrder K)

/-- The coordinate is the integer order reduced modulo n. -/
theorem orderMod_apply (q : Kˣ) :
    (orderMod K n q).toAdd = ((normalizedOrder K q).toAdd : ZMod n) := rfl

/-- An nth power has zero order modulo n. -/
@[simp] theorem orderMod_pow (q : Kˣ) : orderMod K n (q ^ n) = 1 := by
  apply Multiplicative.toAdd.injective
  simp [orderMod_apply, map_pow, nsmul_eq_mul]

/-- A valuation-ring unit has zero order modulo n. -/
@[simp] theorem orderMod_unit (u : (valuation K).valuationSubringˣ) :
    orderMod K n (Units.map (valuation K).valuationSubring.subtype u) = 1 := by
  apply Multiplicative.toAdd.injective
  simp [orderMod_apply]

/-- The order coordinate vanishes exactly when the order is divisible by n. -/
theorem orderMod_eq_one_iff (q : Kˣ) :
    orderMod K n q = 1 ↔ (n : ℤ) ∣ (normalizedOrder K q).toAdd := by
  change ((normalizedOrder K q).toAdd : ZMod n) = 0 ↔ _
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

/-- The order coordinate on the actual multiplicative Kummer quotient. -/
noncomputable def powerClassOrder : PowerClass K n →* Multiplicative (ZMod n) :=
  QuotientGroup.lift _ (orderMod K n) (by
    rintro _ ⟨q, rfl⟩
    exact orderMod_pow K n q)

/-- Formula on a field-unit representative. -/
@[simp] theorem powerClassOrder_mk (q : Kˣ) :
    powerClassOrder K n (powerClassMap n q) = orderMod K n q := rfl

/-- Order divisibility is equivalent to being represented by a valuation-ring unit. -/
theorem isUnitClass_iff_orderMod (q : Kˣ) :
    IsUnitClass (valuation K).valuationSubring n (powerClassMap n q) ↔
      orderMod K n q = 1 := by
  rw [isUnitClass_iff]
  constructor
  · rintro ⟨b, u, rfl⟩
    simpa only [map_mul, orderMod_pow, one_mul, RingHom.toMonoidHom_eq_coe] using
      orderMod_unit K n u
  · intro hq
    obtain ⟨m, hm⟩ := (orderMod_eq_one_iff K n q).mp hq
    obtain ⟨b, hb⟩ := normalizedOrder_surjective K (Multiplicative.ofAdd m)
    have hz : normalizedOrder K (q / b ^ n) = 1 := by
      apply Multiplicative.toAdd.injective
      simp [map_div, map_pow, hb, hm]
    have hu : q / b ^ n ∈ (valuation K).valuationSubring.unitGroup := by
      rw [← normalizedOrder_ker]
      exact hz
    refine ⟨b, (valuation K).valuationSubring.unitGroupMulEquiv ⟨q / b ^ n, hu⟩, ?_⟩
    have he : Units.map (valuation K).valuationSubring.subtype.toMonoidHom
        ((valuation K).valuationSubring.unitGroupMulEquiv ⟨q / b ^ n, hu⟩) = q / b ^ n :=
      Units.ext rfl
    rw [he, mul_div_cancel]

/-- The kernel on Kummer power classes is precisely the independent unit subgroup. -/
theorem powerClassOrder_ker :
    (powerClassOrder K n).ker = unitClasses (valuation K).valuationSubring n := by
  ext x
  induction x using Quotient.inductionOn with | h q =>
    exact (isUnitClass_iff_orderMod K n q).symm

/-- Every residue order occurs on a power class. -/
theorem powerClassOrder_surjective : Function.Surjective (powerClassOrder K n) := by
  intro j
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective j.toAdd
  obtain ⟨q, hq⟩ := normalizedOrder_surjective K (Multiplicative.ofAdd m)
  refine ⟨powerClassMap n q, ?_⟩
  apply Multiplicative.toAdd.injective
  simpa [orderMod_apply, hq] using hm

end LocalClassFieldTheory
