/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.TorsionTensorCompletion
public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivial
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # The actual tensor reductions of the cyclotomic-plus-trivial lattice -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace GaloisRepresentation
variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The coefficient quotient is the actual p-power residue ring. -/
def padicPowerResidue :
    (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ n}) ≃+* ZMod (p ^ n) :=
  (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow n)))

/-- The residue equivalence evaluates the canonical p-adic reduction. -/
@[simp] theorem padicPowerResidue_mk (a : ℤ_[p]) :
    padicPowerResidue p n (Ideal.Quotient.mk _ a) = PadicInt.toZModPow n a := rfl

/-- Actual tensor residues, with the cyclotomic coordinate first. -/
def cyclotomicTrivialReduction :
    PrimePower.Level (V := ℤ_[p] × ℤ_[p]) (p : ℤ_[p]) n ≃+
      ZMod (p ^ n) × ZMod (p ^ n) :=
  ((TensorProduct.prodRight ℤ_[p] ℤ_[p] _ ℤ_[p] ℤ_[p]).trans
    ((TensorProduct.rid ℤ_[p] _).prodCongr (TensorProduct.rid ℤ_[p] _))).toAddEquiv.trans
      ((padicPowerResidue p n).toAddEquiv.prodCongr (padicPowerResidue p n).toAddEquiv)

/-- A reduced lattice vector has its usual two residues. -/
@[simp] theorem cyclotomicTrivialReduction_one_tmul (x : ℤ_[p] × ℤ_[p]) :
    cyclotomicTrivialReduction p n (1 ⊗ₜ[ℤ_[p]] x) =
      (PadicInt.toZModPow n x.1, PadicInt.toZModPow n x.2) := by
  change (padicPowerResidue p n (x.1 • 1), padicPowerResidue p n (x.2 • 1)) = _
  simp [Algebra.smul_def]

/-- The original global Galois action becomes the expected residue action. -/
theorem cyclotomicTrivialReduction_action (g : Field.absoluteGaloisGroup ℚ)
    (x : PrimePower.Level (V := ℤ_[p] × ℤ_[p]) (p : ℤ_[p]) n) :
    cyclotomicTrivialReduction p n
      ((cyclotomicTrivial p g).baseChange (PrimePower.Quot (p : ℤ_[p]) n) x) =
      (PadicInt.toZModPow n (integralCyclotomicScalar p g) *
        (cyclotomicTrivialReduction p n x).1, (cyclotomicTrivialReduction p n x).2) := by
  obtain ⟨v, rfl⟩ := PrimePower.one_tmul_surjective (p : ℤ_[p]) n x
  change cyclotomicTrivialReduction p n (1 ⊗ₜ[ℤ_[p]] (cyclotomicTrivialEnd p g v)) = _
  rw [cyclotomicTrivialEnd_apply, cyclotomicTrivialReduction_one_tmul,
    cyclotomicTrivialReduction_one_tmul, map_mul]

end GaloisRepresentation
