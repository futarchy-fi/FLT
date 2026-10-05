/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ArithmeticGaloisFixedField
public import FLT.Deformations.HardlyRamifiedArithmeticDescent
public import FLT.Deformations.RepresentationTheory.AdjointTateDual
public import FLT.GaloisRepresentation.HardlyRamified.ResidualCharacteristic

/-!
# The actual arithmetic HR adjoint and Tate dual

Use the original framed residual representation on its arithmetic
quotient. Its determinant is the original cyclotomic scalar, so twisting
the contragredient by that determinant gives the arithmetic Tate dual.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open GaloisRepresentation
namespace Deformation
open ProartinianCat
variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  {p : ℕ} [Fact p.Prime] (hp : Odd p)
  [Algebra ℤ_[p] (residueField (𝓞 := O))] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)
local notation "k" => residueField (𝓞 := O)

/-- The arithmetic cyclotomic character extracted from the actual residual determinant. -/
def hardlyArithmeticCyclotomic : HardlyArithmeticGaloisGroup p →* kˣ :=
  Matrix.GeneralLinearGroup.det.comp (hardlyArithmeticResidual O hp hdim ρ hρ).toMonoidHom

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- This character is exactly the original prescribed cyclotomic scalar on G_Q. -/
theorem hardlyArithmeticCyclotomic_original (g : Field.absoluteGaloisGroup ℚ) :
    (hardlyArithmeticCyclotomic O hp hdim ρ hρ (hardlyArithmeticGaloisProjection p g) : k) =
      algebraMap O k (hardlyCyclotomicValue (p := p) O g) :=
  hardlyTwoFramedResidual_det O hp hdim ρ hρ g

/-- The Tate dual of the actual arithmetic trace-zero adjoint, with cyclotomic twist proved. -/
def hardlyArithmeticAdjointDual : Representation k (HardlyArithmeticGaloisGroup p)
    (Module.Dual k (traceZeroAdjoint (hardlyArithmeticResidual O hp hdim ρ hρ).toMonoidHom)) :=
  adjointTateDual (hardlyArithmeticResidual O hp hdim ρ hρ).toMonoidHom
    (hardlyArithmeticCyclotomic O hp hdim ρ hρ)

omit [IsNoetherianRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- Evaluation transforms by the original cyclotomic character, not an unspecified twist. -/
theorem hardlyArithmeticAdjointDual_evaluation (g : Field.absoluteGaloisGroup ℚ)
    (f : Module.Dual k (traceZeroAdjoint
      (hardlyArithmeticResidual O hp hdim ρ hρ).toMonoidHom))
    (X : traceZeroAdjoint (hardlyArithmeticResidual O hp hdim ρ hρ).toMonoidHom) :
    hardlyArithmeticAdjointDual O hp hdim ρ hρ (hardlyArithmeticGaloisProjection p g) f
      (hardlyArithmeticGaloisProjection p g • X) =
        algebraMap O k (hardlyCyclotomicValue (p := p) O g) * f X := by
  rw [hardlyArithmeticAdjointDual, adjointTateDual_evaluation,
    hardlyArithmeticCyclotomic_original]

/-- Oddness of the original prime makes the actual trace pairing perfect. -/
def hardlyArithmeticTraceDualEquiv :
    traceZeroAdjoint (hardlyArithmeticResidual O hp hdim ρ hρ).toMonoidHom ≃ₗ[k]
      Module.Dual k (traceZeroAdjoint
        (hardlyArithmeticResidual O hp hdim ρ hρ).toMonoidHom) := by
  let : Finite k := inferInstanceAs (Finite (IsLocalRing.ResidueField O))
  let : CharP k p := ThreeAdicPlan.charP_of_finite_padic_algebra p k
  have hp2 : 2 < p := by
    have ht := (Fact.out : p.Prime).two_le
    obtain ⟨n, hn⟩ := hp
    omega
  apply traceZeroDualEquiv
  exact (CharP.cast_eq_zero_iff k p 2).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp2)

end Deformation
