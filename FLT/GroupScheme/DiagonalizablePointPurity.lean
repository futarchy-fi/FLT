/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DiagonalizableFiniteFlat
public import FLT.GaloisRepresentation.HardlyRamified.CharacterCyclotomicPurity

/-!
# Cyclotomic action on diagonalizable finite-flat points

Generic points of a finite group algebra evaluate its group-like generators in
roots of unity. The actual cyclotomic character therefore gives their complete
point action at every finite prime-power level.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

/-- The group-like generators in the rational generic fibre of a group algebra. -/
def diagonalGenerator (G : Type) [CommGroup G] :
    G →* ℚ ⊗[ZInvTwo] MonoidAlgebra ZInvTwo G :=
  Algebra.TensorProduct.includeRight.toMonoidHom.comp (MonoidAlgebra.of ZInvTwo G)

/-- A group-algebra generator remains group-like after scalar extension. -/
theorem diagonalGenerator_comul (G : Type) [CommGroup G] (g : G) :
    Coalgebra.comul (R := ℚ) (diagonalGenerator G g) =
      diagonalGenerator G g ⊗ₜ[ℚ] diagonalGenerator G g := by
  change Coalgebra.comul (R := ℚ) (1 ⊗ₜ[ZInvTwo] MonoidAlgebra.single g 1) = _
  simp [diagonalGenerator, TensorProduct.comul_tmul]

/-- Evaluation at a group-like generator is multiplicative for convolution of points. -/
def diagonalEvaluation (G : Type) [CommGroup G] (g : G) :
    (ℚ ⊗[ZInvTwo] MonoidAlgebra ZInvTwo G →ₐ[ℚ] AlgebraicClosure ℚ) →*
      AlgebraicClosure ℚ where
  toFun φ := φ (diagonalGenerator G g)
  map_one' := by
    change algebraMap ℚ (AlgebraicClosure ℚ)
      (Coalgebra.counit (R := ℚ) (diagonalGenerator G g)) = 1
    simp [diagonalGenerator]
  map_mul' φ ψ := by
    change Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _)
      (Coalgebra.comul (R := ℚ) (diagonalGenerator G g)) = _
    rw [diagonalGenerator_comul, Algebra.TensorProduct.lift_tmul]

/-- Algebra maps from a generic group algebra are determined by the group generators. -/
theorem diagonalPoints_ext (G : Type) [CommGroup G]
    {φ ψ : ℚ ⊗[ZInvTwo] MonoidAlgebra ZInvTwo G →ₐ[ℚ] AlgebraicClosure ℚ}
    (h : ∀ g, φ (diagonalGenerator G g) = ψ (diagonalGenerator G g)) : φ = ψ := by
  apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
  apply MonoidAlgebra.algHom_ext
  · intro g
    exact h g
  · exact Subsingleton.elim _ _

/-- If the character group is killed by `m`, so are the actual geometric points
of its diagonalizable model. -/
theorem diagonalizable_points_nsmul (A : Type) [AddCommGroup A] [Finite A]
    (m : ℕ) (hkill : ∀ a : A, m • a = 0)
    (w : (diagonalizableFiniteFlat A).points) : m • w = 0 := by
  apply diagonalPoints_ext (Multiplicative A)
  intro g
  let φ : ℚ ⊗[ZInvTwo] MonoidAlgebra ZInvTwo (Multiplicative A) →ₐ[ℚ]
      AlgebraicClosure ℚ := w.toMul
  change diagonalEvaluation (Multiplicative A) g (φ ^ m) =
    diagonalEvaluation (Multiplicative A) g 1
  rw [map_pow, map_one]
  change (φ (diagonalGenerator (Multiplicative A) g)) ^ m = 1
  have hg : g ^ m = 1 := by
    change Multiplicative.ofAdd (m • g.toAdd) = 1
    rw [hkill]
    rfl
  rw [← map_pow, ← map_pow, hg, map_one, map_one]

/-- The full point action of a finite diagonalizable group killed by `p^n`
is multiplication by the reduction of the p-adic cyclotomic character. -/
theorem diagonalizable_cyclotomic_nsmul (A : Type) [AddCommGroup A] [Finite A]
    (p n : ℕ) [Fact p.Prime] (hkill : ∀ a : A, (p ^ n) • a = 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (w : (diagonalizableFiniteFlat A).points) :
    σ • w =
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv).val.toZModPow n).val • w := by
  apply diagonalPoints_ext (Multiplicative A)
  intro g
  let φ : ℚ ⊗[ZInvTwo] MonoidAlgebra ZInvTwo (Multiplicative A) →ₐ[ℚ]
      AlgebraicClosure ℚ := w.toMul
  have hg : g ^ (p ^ n) = 1 := by
    change Multiplicative.ofAdd ((p ^ n) • g.toAdd) = 1
    rw [hkill]
    rfl
  have hp : (φ (diagonalGenerator (Multiplicative A) g)) ^ (p ^ n) = 1 := by
    rw [← map_pow, ← map_pow, hg, map_one, map_one]
  have he := cyclotomicCharacter.spec p σ.toRingEquiv _ hp
  change σ (φ (diagonalGenerator (Multiplicative A) g)) =
    diagonalEvaluation (Multiplicative A) g
      (φ ^ ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv).val.toZModPow n).val)
  rw [map_pow]
  exact he

/-- A diagonalizable finite-flat model has cyclotomic scalar action on its
full point group, with the canonical action of the p-adic integers. -/
theorem diagonalizable_pure_cyclotomic (A : Type) [AddCommGroup A] [Finite A]
    (p n : ℕ) [Fact p.Prime] (hkill : ∀ a : A, (p ^ n) • a = 0) :
    letI := primePowerModule p n (diagonalizable_points_nsmul A (p ^ n) hkill)
    Pure (diagonalizableFiniteFlat A).points
      (fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ ↦
        (cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv).val) := by
  let := primePowerModule p n (diagonalizable_points_nsmul A (p ^ n) hkill)
  intro σ w
  rw [primePowerModule_smul]
  exact diagonalizable_cyclotomic_nsmul A p n hkill σ w

/-- The geometric points of the cube-root group scheme are killed by three. -/
theorem muThree_nsmul (w : muThree.points) : (3 : ℕ) • w = 0 := by
  apply diagonalizable_points_nsmul (ZMod 3) 3 _ w
  intro a
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The full action on the cube-root group scheme is the three-adic cyclotomic
character, acting through reduction modulo three. -/
theorem muThree_pure_cyclotomic :
    letI := primePowerModule 3 1 (fun w : muThree.points ↦ by simpa using muThree_nsmul w)
    Pure muThree.points (fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ ↦
      (cyclotomicCharacter (AlgebraicClosure ℚ) 3 σ.toRingEquiv).val) := by
  let := primePowerModule 3 1 (fun w : muThree.points ↦ by simpa using muThree_nsmul w)
  intro σ w
  rw [primePowerModule_smul]
  apply diagonalizable_cyclotomic_nsmul (ZMod 3) 3 1 _ σ w
  intro a
  simp only [pow_one]
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end ThreeAdicPlan
