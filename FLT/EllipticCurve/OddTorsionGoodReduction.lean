/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.OddTorsionFlat
public import FLT.EllipticCurve.Torsion
public import FLT.TateCurve.ModelTransport
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Good reduction with integral two-torsion

Short normalization and equivariant model transport turn the explicit odd-torsion
Hopf order into a finite-flat model for the torsion representation. In particular,
this applies to good-reduction models with `a₃ = a₆ = 0` when 2 and 3 are units.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
namespace WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  [Invertible (2 : R)] [Invertible (3 : R)]
/-- Short normalization carries the two-torsion point at the origin to an integral point. -/
theorem shortModel_twoTorsion_equation (h3 : W.a₃ = 0) (h6 : W.a₆ = 0) :
    (W.toShortNF • W).toAffine.Equation
      (⅟3 * (W.toCharNeTwoNF • W).a₂) 0 := by
  have h6' : (W.toCharNeTwoNF • W).a₆ = 0 := by
    simp [toCharNeTwoNF, variableChange_a₆, h3, h6]
  rw [toShortNF, mul_smul]
  generalize hu : W.toCharNeTwoNF • W = U at *
  rw [Affine.equation_iff]
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_one, inv_one, one_pow,
    one_mul, zero_mul, mul_zero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [h6']
  ring
end WeierstrassCurve
namespace AddEquiv
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
/-- An additive equivalence restricts to the subgroups killed by a fixed natural number. -/
def torsionByEquiv (e : A ≃+ B) (n : ℕ) :
    AddSubgroup.torsionBy A (n : ℤ) ≃+ AddSubgroup.torsionBy B (n : ℤ) where
  toFun P := ⟨e P.val, AddSubgroup.torsionBy.nsmul_iff.mpr (by
    rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp P.property, map_zero])⟩
  invFun P := ⟨e.symm P.val, AddSubgroup.torsionBy.nsmul_iff.mpr (by
    rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp P.property, map_zero])⟩
  left_inv P := Subtype.ext (e.symm_apply_apply _)
  right_inv P := Subtype.ext (e.apply_symm_apply _)
  map_add' P Q := Subtype.ext (map_add _ _ _)
end AddEquiv
namespace WeierstrassCurve
universe u
variable {R K : Type u} [CommRing R] [IsDedekindDomain R]
  [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
  (W : WeierstrassCurve R) [W.IsShortNF] (E : WeierstrassCurve K) [E.IsElliptic]
set_option backward.isDefEq.respectTransparency false in
/-- A short integral model identifies a finite-flat model of geometric odd torsion. -/
theorem isFiniteFlat_torsion_of_short_model (n : ℕ) (hn : Odd n) (hnpos : 0 < n)
    (hΔ : IsUnit W.Δ) (h2 : IsUnit (2 : R)) (ξ : R) (ht : W.toAffine.Equation ξ 0)
    (C : VariableChange K) (h : W.map (algebraMap R K) = C • E) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) (E.galoisRep n hnpos).Space := by
  let k := AlgebraicClosure K
  let : W.IsElliptic := ⟨hΔ⟩
  let : Module.IsTorsionFree R k := Module.IsTorsionFree.trans_faithfulSMul R K k
  have hgeo : W.map (algebraMap R k) = (C • E).map (algebraMap K k) := by
    rw [← h, map_map, ← IsScalarTower.algebraMap_eq]
  let a := Affine.Point.equivOfEq hgeo
  let b := Affine.Point.equivVariableChangeOver (L := k) E C
  let e := (a.trans b).torsionByEquiv n
  have hT : (W.map (algebraMap R k)).toAffine.Nonsingular
      (algebraMap R k ξ) (algebraMap R k 0) :=
    Affine.equation_iff_nonsingular.mp (ht.map (algebraMap R k))
  have htwo : 2 • Affine.Point.some _ _ hT = 0 := by
    rw [two_nsmul]
    apply Affine.Point.add_self_of_Y_eq
    simp [Affine.negY]
  apply W.isFiniteFlat_of_short_twoTorsion hn ξ hT htwo K hΔ h2 ht
    (X := (E.galoisRep n hnpos).Space) e
  intro σ P
  apply Subtype.ext
  change b (a (Affine.Point.map (σ.toAlgHom.restrictScalars R) P.val)) =
    Affine.Point.map σ.toAlgHom (b (a P.val))
  rw [Affine.Point.map_equivVariableChangeOver]
  apply congrArg b
  cases P.val with
  | zero => simp only [← Affine.Point.zero_def, map_zero]
  | some x y hns =>
    simp only [a, Affine.Point.map_some, Affine.Point.equivOfEq_some]
    rfl
end WeierstrassCurve
namespace WeierstrassCurve
universe u
variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
  (E : WeierstrassCurve K) [E.IsElliptic] [E.HasGoodReduction R]
  [Invertible (2 : R)] [Invertible (3 : R)]
/-- Good reduction and two-torsion at the origin give finite-flat odd torsion
when two and three are invertible in the coefficient ring. -/
theorem isFiniteFlat_torsion_of_goodReduction_twoTorsion
    (h3 : E.a₃ = 0) (h6 : E.a₆ = 0) (n : ℕ) (hn : Odd n) (hnpos : 0 < n) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) (E.galoisRep n hnpos).Space := by
  let W := integralModel R E
  have hW : W.map (algebraMap R K) = E := baseChange_integralModel_eq R E
  have hW3 : W.a₃ = 0 := by
    apply IsFractionRing.injective R K
    simpa only [W, map_zero, h3] using integralModel_a₃_eq R E
  have hW6 : W.a₆ = 0 := by
    apply IsFractionRing.injective R K
    simpa only [W, map_zero, h6] using integralModel_a₆_eq R E
  have hred : (E.reduction R).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
  have hΔ : IsUnit W.Δ := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    have hd := (E.reduction R).isUnit_Δ
    simpa only [reduction, map_Δ, isUnit_iff_ne_zero] using hd
  let : W.IsElliptic := ⟨hΔ⟩
  apply (W.toShortNF • W).isFiniteFlat_torsion_of_short_model E n hn hnpos
    (W.toShortNF • W).isUnit_Δ (isUnit_of_invertible (2 : R))
    (⅟3 * (W.toCharNeTwoNF • W).a₂) (W.shortModel_twoTorsion_equation hW3 hW6)
    (W.toShortNF.map (algebraMap R K))
  rw [← map_variableChange, hW]
end WeierstrassCurve
