/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerHopf

/-!
# Geometric points of the Kummer Hopf algebra

Restriction from the generic fibre respects convolution. Unit-root coordinates
make this group law and the Galois action explicit.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace KummerAlgebra

universe v
variable (R : Type v) [CommRing R] (n : ℕ) (u : Rˣ) (hn : 0 < n)
variable {S : Type v} [CommRing S] [Algebra R S] [IsDomain S]

/-- The unit-root point is the inverse of the coordinate equivalence. -/
theorem coordinateUnitPointsEquiv_symm_apply
    (a : {ix : Fin n × Sˣ // ix.2 ^ n = (Units.map (algebraMap R S) u) ^ ix.1.val}) :
    (coordinateUnitPointsEquiv R n u hn).symm a =
      rootPoint R n u a.val.1 (a.val.2 : S) (by simpa using congrArg Units.val a.property) := rfl

/-- Reading the coordinates of a unit-root point recovers that root and its component. -/
theorem coordinateUnitPointsEquiv_rootPoint
    (a : {ix : Fin n × Sˣ // ix.2 ^ n = (Units.map (algebraMap R S) u) ^ ix.1.val}) :
    coordinateUnitPointsEquiv R n u hn
      (rootPoint R n u a.val.1 (a.val.2 : S) (by simpa using congrArg Units.val a.property)) = a :=
  (coordinateUnitPointsEquiv R n u hn).apply_symm_apply a

/-- Multiplication of unit-root coordinates, including the carry factor. -/
noncomputable def mulUnitPoint
    (a b : {ix : Fin n × Sˣ // ix.2 ^ n = (Units.map (algebraMap R S) u) ^ ix.1.val}) :
    {ix : Fin n × Sˣ // ix.2 ^ n = (Units.map (algebraMap R S) u) ^ ix.1.val} :=
  ⟨(sumComponent n hn a.val.1 b.val.1,
    a.val.2 * b.val.2 * (Units.map (algebraMap R S) u)⁻¹ ^
      ((a.val.1.val + b.val.1.val) / n)), by
    apply Units.ext
    have ha : (a.val.2 : S) ^ n = algebraMap R S ((u : R) ^ a.val.1.val) := by
      simpa using congrArg Units.val a.property
    have hb : (b.val.2 : S) ^ n = algebraMap R S ((u : R) ^ b.val.1.val) := by
      simpa using congrArg Units.val b.property
    simpa only [← map_inv, Units.val_pow_eq_pow_val, Units.val_mul, Units.coe_map,
      MonoidHom.coe_ofClass, map_pow, sumComponent] using
      mul_carry_pow R n u ha hb (Nat.mod_add_div _ _).symm⟩

/-- Unit-root coordinates identify convolution with the carry multiplication. -/
theorem coordinateUnitPointsEquiv_convolution
    (a b : {ix : Fin n × Sˣ // ix.2 ^ n = (Units.map (algebraMap R S) u) ^ ix.1.val}) :
    convolution R n u hn ((coordinateUnitPointsEquiv R n u hn).symm a)
      ((coordinateUnitPointsEquiv R n u hn).symm b) =
        (coordinateUnitPointsEquiv R n u hn).symm (mulUnitPoint R n u hn a b) := by
  simp only [coordinateUnitPointsEquiv_symm_apply, convolution_rootPoint]
  apply rootPoint_congr R n u rfl
  simp [mulUnitPoint, ← map_inv]

/-- An algebra automorphism acts on unit-root coordinates by acting on the root. -/
noncomputable def mapUnitPoint (σ : S →ₐ[R] S)
    (a : {ix : Fin n × Sˣ // ix.2 ^ n = (Units.map (algebraMap R S) u) ^ ix.1.val}) :
    {ix : Fin n × Sˣ // ix.2 ^ n = (Units.map (algebraMap R S) u) ^ ix.1.val} :=
  ⟨(a.val.1, Units.map σ.toRingHom.toMonoidHom a.val.2), by
    apply Units.ext
    have h := congrArg (fun x : Sˣ ↦ σ (x : S)) a.property
    simpa using h⟩

/-- The coordinate equivalence commutes with algebra maps on the target. -/
theorem coordinateUnitPointsEquiv_comp (σ : S →ₐ[R] S)
    (a : {ix : Fin n × Sˣ // ix.2 ^ n = (Units.map (algebraMap R S) u) ^ ix.1.val}) :
    σ.comp ((coordinateUnitPointsEquiv R n u hn).symm a) =
      (coordinateUnitPointsEquiv R n u hn).symm (mapUnitPoint R n u σ a) := by
  simp only [coordinateUnitPointsEquiv_symm_apply, comp_rootPoint]
  apply rootPoint_congr R n u rfl
  rfl

end KummerAlgebra

namespace Bialgebra

universe v
variable (R K L H : Type v) [CommRing R] [Field K] [Field L] [CommRing H]
variable [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Bialgebra R H]

/-- Restriction of generic-fibre points to the integral coordinate algebra. -/
noncomputable def restrictPoints : (K ⊗[R] H →ₐ[K] L) ≃ (H →ₐ[R] L) :=
  (Algebra.TensorProduct.liftEquivRight R K H L).symm

/-- Restriction to the coefficient-ring model preserves convolution. -/
theorem restrictPoints_mul (f g : K ⊗[R] H →ₐ[K] L) :
    restrictPoints R K L H (f * g) =
      (Algebra.TensorProduct.lift (restrictPoints R K L H f) (restrictPoints R K L H g)
        (fun _ _ ↦ .all _ _)).comp (comulAlgHom R H) := by
  apply AlgHom.ext
  intro a
  change Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)
      (comulAlgHom K (K ⊗[R] H) (Algebra.TensorProduct.includeRight a)) = _
  have hc := RingHom.congr_fun (comul_includeRight (R := R) (A := K) (B := H)) a
  rw [show comulAlgHom K (K ⊗[R] H) (Algebra.TensorProduct.includeRight a) = _ from hc]
  change Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)
      (Algebra.TensorProduct.mapRingHom _ _ _
        (by simp [← IsScalarTower.algebraMap_eq])
        (by simp [← IsScalarTower.algebraMap_eq]) (comulAlgHom R H a)) =
    Algebra.TensorProduct.lift (restrictPoints R K L H f) (restrictPoints R K L H g)
      (fun _ _ ↦ .all _ _) (comulAlgHom R H a)
  induction comulAlgHom R H a using TensorProduct.inductionOn with
  | add a b ha hb => simp_all
  | tmul a b => simp [restrictPoints, Algebra.TensorProduct.mapRingHom_tmul]

end Bialgebra
