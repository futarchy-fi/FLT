/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivial
public import FLT.GaloisRepresentation.HardlyRamified.InertiaTwoSquareZero

/-! # Ramification and the actual tame quotient of the standard integral member -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation
variable (p : ℕ) [Fact p.Prime]

/-- The trivial local line used as the quotient at two. -/
def trivialLocalLine : GaloisRep ℚ_[2] ℤ_[p] ℤ_[p] := by
  letI := moduleTopology ℤ_[p] (Module.End ℤ_[p] ℤ_[p])
  exact
    { toFun := fun _ ↦ 1
      map_one' := rfl
      map_mul' := fun _ _ ↦ (one_mul _).symm
      continuous_toFun := continuous_const }

/-- Every prime distinct from p is unramified for the standard representation. -/
theorem cyclotomicTrivial_unramified (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    (cyclotomicTrivial p).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat where
  localInertiaGroup_le := by
    intro g hg
    simp only [GaloisRep.ker, MonoidHom.mem_ker]
    dsimp [GaloisRep.toLocal, GaloisRep.map, ContinuousMonoidHom.comp, cyclotomicTrivial]
    apply LinearMap.ext
    intro x
    change cyclotomicTrivialEnd p _ x = x
    rw [cyclotomicTrivialEnd_apply]
    have h := ThreeAdicPlan.cyclotomicCharacter_localInertia p q hq hqp g hg
    simp only [integralCyclotomicScalar_apply, h, one_mul]

/-- The second-coordinate quotient proves the precise tame-at-two clause. -/
theorem cyclotomicTrivial_tameAtTwo :
    ∃ (π : (ℤ_[p] × ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] ℤ_[p] ℤ_[p]),
      ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (x : ℤ_[p] × ℤ_[p]),
        π ((cyclotomicTrivial p).map (algebraMap ℚ ℚ_[2]) g x) = δ g (π x) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
          (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧ (∀ g, δ g * δ g = 1) := by
  refine ⟨LinearMap.snd ℤ_[p] ℤ_[p] ℤ_[p], cyclotomicTrivial_snd_surjective p,
    trivialLocalLine p, fun g x ↦ ⟨?_, ?_, ?_⟩⟩
  · exact cyclotomicTrivial_snd p _ x
  · intro σ _
    rfl
  · intro σ
    exact one_mul _

end GaloisRepresentation
