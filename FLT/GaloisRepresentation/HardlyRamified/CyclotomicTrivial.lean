/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! # The integral cyclotomic-plus-trivial representation

This constructs the proposed standard members of the three-adic family
route. It does not replace any original nonsplit member by its direct sum.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation
variable (p : ℕ) [Fact p.Prime]

/-- The cyclotomic scalar as a continuous character of the rational Galois group. -/
def integralCyclotomicScalar : Field.absoluteGaloisGroup ℚ →ₜ* ℤ_[p] where
  toMonoidHom := (Units.coeHom ℤ_[p]).comp
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p).comp
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ) (AlgebraicClosure ℚ)))
  continuous_toFun := Units.continuous_val.comp (cyclotomicCharacter.continuous p ℚ _)

/-- The continuous scalar is the actual cyclotomic character, with the chosen Galois convention. -/
theorem integralCyclotomicScalar_apply (g : Field.absoluteGaloisGroup ℚ) :
    integralCyclotomicScalar p g =
      (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv : ℤ_[p]) := rfl

/-- The endomorphism acting cyclotomically on the first coordinate and trivially on the second. -/
def cyclotomicTrivialEnd (g : Field.absoluteGaloisGroup ℚ) :
    Module.End ℤ_[p] (ℤ_[p] × ℤ_[p]) :=
  integralCyclotomicScalar p g •
    ((LinearMap.inl ℤ_[p] ℤ_[p] ℤ_[p]).comp (LinearMap.fst ℤ_[p] ℤ_[p] ℤ_[p])) +
    (LinearMap.inr ℤ_[p] ℤ_[p] ℤ_[p]).comp (LinearMap.snd ℤ_[p] ℤ_[p] ℤ_[p])

/-- The actual action on the two coordinates. -/
@[simp] theorem cyclotomicTrivialEnd_apply (g : Field.absoluteGaloisGroup ℚ)
    (x : ℤ_[p] × ℤ_[p]) :
    cyclotomicTrivialEnd p g x = (integralCyclotomicScalar p g * x.1, x.2) := by
  simp [cyclotomicTrivialEnd]

/-- The continuous integral rank-two representation used away from the original member. -/
def cyclotomicTrivial : GaloisRep ℚ ℤ_[p] (ℤ_[p] × ℤ_[p]) := by
  letI := moduleTopology ℤ_[p] (Module.End ℤ_[p] (ℤ_[p] × ℤ_[p]))
  letI : ContinuousAdd (Module.End ℤ_[p] (ℤ_[p] × ℤ_[p])) :=
    IsModuleTopology.toContinuousAdd ℤ_[p] _
  refine
    { toFun := cyclotomicTrivialEnd p
      map_one' := ?_
      map_mul' := ?_
      continuous_toFun := ?_ }
  · apply LinearMap.ext
    intro x
    simp
  · intro g h
    apply LinearMap.ext
    intro x
    simp [Module.End.mul_apply, mul_assoc]
  · exact ((integralCyclotomicScalar p).continuous.smul continuous_const).add continuous_const

/-- The chosen integral space has rank two. -/
theorem cyclotomicTrivial_rank : Module.rank ℤ_[p] (ℤ_[p] × ℤ_[p]) = 2 := by
  simp only [rank_prod', Module.rank_self]
  norm_num

/-- Projection onto the trivial summand is an actual surjective quotient. -/
theorem cyclotomicTrivial_snd_surjective :
    Function.Surjective (LinearMap.snd ℤ_[p] ℤ_[p] ℤ_[p]) := fun x ↦ ⟨(0, x), rfl⟩

/-- The quotient action is trivial, including for every local restriction. -/
theorem cyclotomicTrivial_snd (g : Field.absoluteGaloisGroup ℚ) (x : ℤ_[p] × ℤ_[p]) :
    (cyclotomicTrivial p g x).2 = x.2 := by
  change (cyclotomicTrivialEnd p g x).2 = x.2
  rw [cyclotomicTrivialEnd_apply]

end GaloisRepresentation
