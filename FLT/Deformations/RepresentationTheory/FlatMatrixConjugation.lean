/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CoordinateChange

/-!
# Finite flatness under matrix recovery frames

Translate a matrix conjugacy into the linear coordinate change used by the
finite-flat model API, retaining the same coefficient ring.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FramedGaloisRep
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLocalRing A] {n : Type} [Fintype n] [DecidableEq n]
  (ρ τ : FramedGaloisRep ℚ A n) (P : GL n A)

omit [IsLocalRing A] in
/-- A matrix recovery frame gives exactly the corresponding linear conjugacy. -/
theorem conj_eq_of_matrix_recovery
    (h : ∀ g, P * ρ.GL g * P⁻¹ = τ.GL g) :
    ρ.conj P.toLin.toLinearEquiv = τ := by
  ext g : 1
  apply LinearMap.ext
  intro x
  have he := congrArg (fun M : GL n A ↦ (M.toLin : Module.End A (n → A)) x) (h g)
  simp only [map_mul, map_inv, Units.val_mul, Module.End.mul_apply,
    ← ofGL_apply, ofGL, Equiv.symm_apply_apply] at he
  exact he

/-- Finite-flat reductions are invariant under a specified matrix recovery frame. -/
theorem isFlatAt_iff_of_matrix_recovery
    (h : ∀ g, P * ρ.GL g * P⁻¹ = τ.GL g)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ρ.IsFlatAt v ↔ τ.IsFlatAt v := by
  constructor
  · intro hρ
    rw [← conj_eq_of_matrix_recovery ρ τ P h]
    exact hρ.conj ρ P.toLin.toLinearEquiv v
  · intro hτ
    have hi : ∀ g, P⁻¹ * τ.GL g * (P⁻¹)⁻¹ = ρ.GL g := by
      intro g
      rw [← h g]
      simp [mul_assoc]
    rw [← conj_eq_of_matrix_recovery τ ρ P⁻¹ hi]
    exact hτ.conj τ (P⁻¹).toLin.toLinearEquiv v

end FramedGaloisRep
