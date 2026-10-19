/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluTargetWitness
public import FLT.FreyCurve.Serre.QuotientIntegralSums
public import FLT.FreyCurve.Serre.VeluDivisionIntegrality
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integrality of the actual Frey Vélu targets away from p

The integer Frey equation and its division polynomial prove integrality of
all kernel abscissae wherever p is invertible. The paired sums then descend
to the actual rational target. No kernel-coordinate assumption is needed.
-/

@[expose] public section

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace FreyPackage

variable (P : FreyPackage) (R : Type*) [CommRing R] [Algebra R ℚ]

/-- All five source coefficients are integral over any coefficient ring acting on ℚ. -/
theorem frey_coefficients_isIntegral :
    IsIntegral R P.freyCurve.a₁ ∧ IsIntegral R P.freyCurve.a₂ ∧
      IsIntegral R P.freyCurve.a₃ ∧ IsIntegral R P.freyCurve.a₄ ∧
        IsIntegral R P.freyCurve.a₆ := by
  rw [← FreyCurve.map P]
  exact ⟨isIntegral_intCast _, isIntegral_intCast _, isIntegral_intCast _,
    isIntegral_intCast _, isIntegral_intCast _⟩

/-- The source b-invariants are integral because the normalized Frey model is integral. -/
theorem frey_b_invariants_isIntegral :
    IsIntegral R P.freyCurve.b₂ ∧ IsIntegral R P.freyCurve.b₄ ∧
      IsIntegral R P.freyCurve.b₆ := by
  rw [← FreyCurve.map P, map_b₂, map_b₄, map_b₆]
  exact ⟨isIntegral_intCast _, isIntegral_intCast _, isIntegral_intCast _⟩

variable [Nontrivial R]

omit [Nontrivial R] in
/-- The geometric Frey equation is also obtained from its integral model over R. -/
theorem frey_integral_model_map :
    (P.freyCurveInt.map (algebraMap ℤ R)).map (algebraMap R (AlgebraicClosure ℚ)) =
      P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ)) := by
  rw [← FreyCurve.map P, WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  congr 1
  exact Subsingleton.elim _ _

/-- Actual geometric Frey kernel coordinates are integral whenever p is a unit. -/
theorem velu_kernel_xCoord_isIntegral (hp : IsUnit (P.p : R))
    (q : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p →ₗ[ZMod P.p]
      ZMod P.p) (Q : Velu.torsionKernel P.freyCurve P.p q) :
    IsIntegral R (Velu.xCoord Q.val) := by
  exact Velu.torsion_xCoord_isIntegral (P.freyCurveInt.map (algebraMap ℤ R)) _
    (P.frey_integral_model_map R) P.hp_odd hp Q.val
    (Velu.torsionKernel_killed P.freyCurve P.p q Q.val Q.property)

variable {P R} {E : WeierstrassCurve ℚ}

/-- The actual rational Frey target has integral coefficients away from the kernel prime. -/
theorem IsVeluTarget.coefficients_isIntegral (h : P.IsVeluTarget E) (hp : IsUnit (P.p : R)) :
    IsIntegral R E.a₁ ∧ IsIntegral R E.a₂ ∧ IsIntegral R E.a₃ ∧
      IsIntegral R E.a₄ ∧ IsIntegral R E.a₆ := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := P.frey_coefficients_isIntegral R
  obtain ⟨hb₂, hb₄, hb₆⟩ := P.frey_b_invariants_isIntegral R
  rcases h with rfl | ⟨q, _, _, heq⟩
  · exact ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩
  · obtain ⟨h₄, h₆⟩ := heq.a₄_a₆_isIntegral P.hp_odd hb₂ hb₄ hb₆ ha₄ ha₆
      (fun Q _ ↦ P.velu_kernel_xCoord_isIntegral R hp q Q)
    exact ⟨by simpa only [heq.a₁] using ha₁, by simpa only [heq.a₂] using ha₂,
      by simpa only [heq.a₃] using ha₃, h₄, h₆⟩

/-- Over an integrally closed coefficient ring with fraction field ℚ, the actual target
has an integral equation whenever the kernel prime is a unit. -/
theorem IsVeluTarget.exists_integral_model [IsFractionRing R ℚ]
    [IsIntegrallyClosed R] (h : P.IsVeluTarget E) (hp : IsUnit (P.p : R)) :
    ∃ U : WeierstrassCurve R, U.map (algebraMap R ℚ) = E := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := h.coefficients_isIntegral hp
  obtain ⟨a₁, ha₁⟩ := IsIntegrallyClosed.isIntegral_iff.mp h₁
  obtain ⟨a₂, ha₂⟩ := IsIntegrallyClosed.isIntegral_iff.mp h₂
  obtain ⟨a₃, ha₃⟩ := IsIntegrallyClosed.isIntegral_iff.mp h₃
  obtain ⟨a₄, ha₄⟩ := IsIntegrallyClosed.isIntegral_iff.mp h₄
  obtain ⟨a₆, ha₆⟩ := IsIntegrallyClosed.isIntegral_iff.mp h₆
  refine ⟨⟨a₁, a₂, a₃, a₄, a₆⟩, ?_⟩
  ext <;> assumption

end FreyPackage
