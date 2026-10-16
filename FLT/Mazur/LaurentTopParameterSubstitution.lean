/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonLaurentTopCoefficient
public import FLT.Mazur.PolygonStageTopScalar
public import FLT.Mazur.LaurentUnitPoints

/-!
# Exact Laurent substitution in the adjacent top layer

The original parameter annihilator is the adjacent restriction kernel.
Substitutions agreeing at the preceding stage therefore agree on every
parameter multiple, and products of arbitrary such defects vanish.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentUnitPoints PolygonScalingNaturality LaurentCoefficientEvaluation
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "L" => (S)[T;T⁻¹]
local notation "r" => coeffMap (AlgHom.toRingHom (restriction R m))

/-- Parameter annihilation is precisely vanishing at the preceding Laurent stage. -/
theorem topLaurent_parameter_eq_zero_iff (p : L) :
    C (e) * p = 0 ↔ (r) p = 0 := by
  constructor
  · intro hp
    ext d
    have hd := congrArg (fun q : L ↦ q.coeff d) hp
    simp only [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply,
      smul_eq_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hd
    exact (coeffMap_coeff _ p d).trans ((parameter_mul_eq_zero_iff R m _).mp hd)
  · intro hp
    ext d
    rw [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    apply (parameter_mul_eq_zero_iff R m _).mpr
    change (restriction R m).toRingHom (p.coeff d) = 0
    have hd := congrArg (fun q : (Ring R m)[T;T⁻¹] ↦ q.coeff d) hp
    simpa only [coeffMap_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hd

/-- Equal adjacent-stage Laurent values have equal parameter multiples. -/
theorem topLaurent_parameter_eq (p q : L) (hpq : (r) p = (r) q) :
    C (e) * p = C (e) * q := by
  apply sub_eq_zero.mp
  rw [← mul_sub, topLaurent_parameter_eq_zero_iff, map_sub, hpq, sub_self]

/-- Substitution at the preceding stage depends only on the restricted coordinate unit. -/
theorem topLaurent_evalUnit_restriction_eq (u v : (L)ˣ)
    (huv : (r) u.val = (r) v.val) (p : L) :
    (r) (evalUnit u p) = (r) (evalUnit v p) := by
  have he : Units.map (r).toMonoidHom u = Units.map (r).toMonoidHom v := Units.ext huv
  have hi : (r) u⁻¹.val = (r) v⁻¹.val :=
    congrArg (fun w : (Ring R m)[T;T⁻¹]ˣ ↦ w⁻¹.val) he
  have hm : (r).comp (evalUnit (R := S) u).toRingHom =
      (r).comp (evalUnit (R := S) v).toRingHom := by
    apply ringHom_ext
    · intro s
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evalUnit_C]
    · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        evalUnit_T, zpow_one] using huv
    · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        evalUnit_T, zpow_neg_one] using hi
  exact RingHom.congr_fun hm p

/-- Both whole substitutions coincide on the original parameter ideal. -/
theorem topLaurent_evalUnit_weighted_eq (u v : (L)ˣ)
    (huv : (r) u.val = (r) v.val) (p : L) :
    evalUnit u (C (e) * p) = evalUnit v (C (e) * p) := by
  rw [map_mul, map_mul, evalUnit_C, evalUnit_C]
  exact topLaurent_parameter_eq R m _ _ (topLaurent_evalUnit_restriction_eq R m u v huv p)

/-- The actual top coefficient reconstructs every adjacent-kernel Laurent function. -/
theorem topLaurent_annihilator_reconstruct (p : L) (hp : C (e) * p = 0) :
    p = C ((e) ^ (m + 1)) * coeffMap (algebraMap R (S))
      (laurentStageCoeff R (m + 1) (m + 1) p) := by
  have hz := (topLaurent_parameter_eq_zero_iff R m p).mp hp
  ext d
  rw [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeffMap_coeff]
  apply restriction_kernel_top
  change (restriction R m).toRingHom (p.coeff d) = 0
  have hd := congrArg (fun q : (Ring R m)[T;T⁻¹] ↦ q.coeff d) hz
  simpa only [coeffMap_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hd

/-- The entire parameter annihilator has square zero at every positive stage. -/
theorem topLaurent_annihilator_mul (p q : L)
    (hp : C (e) * p = 0) (hq : C (e) * q = 0) : p * q = 0 := by
  have hs : (C ((e) ^ (m + 1)) : L) ^ 2 = 0 := by
    rw [← map_pow]
    have he : ((e) ^ (m + 1)) ^ 2 = 0 := by
      simpa using parameter_top_weight_sq R m (S)
    rw [he, map_zero]
  rw [topLaurent_annihilator_reconstruct R m p hp,
    topLaurent_annihilator_reconstruct R m q hq, mul_mul_mul_comm]
  rw [← pow_two, hs, zero_mul]

/-- Both full punctured branches retain the same square-zero annihilator property. -/
theorem topNodePair_annihilator_mul (p q : (L) × (L))
    (hp : (e) • p = 0) (hq : (e) • q = 0) : p * q = 0 := by
  apply Prod.ext
  · exact topLaurent_annihilator_mul R m p.1 q.1
      ((smul_eq_C_mul _ _).symm.trans (congrArg Prod.fst hp))
      ((smul_eq_C_mul _ _).symm.trans (congrArg Prod.fst hq))
  · exact topLaurent_annihilator_mul R m p.2 q.2
      ((smul_eq_C_mul _ _).symm.trans (congrArg Prod.snd hp))
      ((smul_eq_C_mul _ _).symm.trans (congrArg Prod.snd hq))

end FLT.Mazur.PolygonInfinitesimalStages
