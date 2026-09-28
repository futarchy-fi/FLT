/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantMuThreeTorsion
public import FLT.GroupScheme.ConstantMuThreeGlobalSplitting

/-!
# Cubic coordinates on the actual cube-root point group

Evaluation at the generator gives an injective equivariant map from the
existing geometric points of `μ₃` to cube roots of unity. A choice of additive
coordinates identifies its contragredient with the same point group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- Evaluation at the standard character of the cube-root group. -/
def muThreeValue (w : muThree.points) : AlgebraicClosure ℚ :=
  diagonalEvaluation (Multiplicative (ZMod 3)) (Multiplicative.ofAdd 1) w.toMul

/-- Evaluation of every cube-root point is a cube root of unity. -/
theorem muThreeValue_cube (w : muThree.points) : muThreeValue w ^ 3 = 1 := by
  let φ : ℚ ⊗[ZInvTwo] MonoidAlgebra ZInvTwo (Multiplicative (ZMod 3)) →ₐ[ℚ]
      AlgebraicClosure ℚ := w.toMul
  change φ (diagonalGenerator (Multiplicative (ZMod 3)) (Multiplicative.ofAdd 1)) ^ 3 = 1
  rw [← map_pow, ← map_pow]
  have hg : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by decide
  rw [hg, map_one, map_one]

/-- Cube-root evaluations are nonzero. -/
theorem muThreeValue_ne_zero (w : muThree.points) : muThreeValue w ≠ 0 := by
  intro h
  have hc := muThreeValue_cube w
  rw [h, zero_pow (by decide : 3 ≠ 0)] at hc
  exact zero_ne_one hc

/-- The actual cube-root point group, evaluated in the units of the algebraic closure. -/
def muThreeUnit : Multiplicative muThree.points →* (AlgebraicClosure ℚ)ˣ where
  toFun w := Units.mk0 (muThreeValue w.toAdd) (muThreeValue_ne_zero w.toAdd)
  map_one' := by
    apply Units.ext
    exact (diagonalEvaluation _ _).map_one
  map_mul' w v := by
    apply Units.ext
    exact (diagonalEvaluation _ _).map_mul w.toAdd.toMul v.toAdd.toMul

/-- Unit-valued evaluation commutes with rational Galois action. -/
theorem muThreeUnit_smul (σ : Γ) (w : muThree.points) :
    muThreeUnit (Multiplicative.ofAdd (σ • w)) = σ • muThreeUnit (Multiplicative.ofAdd w) := by
  apply Units.ext
  rfl

/-- The image of unit-valued evaluation is killed by cubing. -/
theorem muThreeUnit_cube (w : muThree.points) : muThreeUnit (Multiplicative.ofAdd w) ^ 3 = 1 := by
  apply Units.ext
  exact muThreeValue_cube w

/-- The standard character separates all points of `μ₃`. -/
theorem muThreeValue_injective : Function.Injective muThreeValue := by
  intro w v h
  apply diagonalPoints_ext (Multiplicative (ZMod 3))
  intro g
  have hg : g = (Multiplicative.ofAdd (1 : ZMod 3)) ^ g.toAdd.val := by
    apply Multiplicative.toAdd.injective
    change g.toAdd = g.toAdd.val • (1 : ZMod 3)
    simp [nsmul_eq_mul]
  rw [hg]
  simp only [map_pow]
  exact congrArg (fun z : AlgebraicClosure ℚ ↦ z ^ g.toAdd.val) h

/-- Unit-valued evaluation is injective. -/
theorem muThreeUnit_injective : Function.Injective muThreeUnit := by
  intro w v h
  apply Multiplicative.toAdd.injective
  exact muThreeValue_injective (congrArg Units.val h)

/-- Additive coordinates on the three-element cube-root point group. -/
def muThreeCoordinates : ZMod 3 ≃+ muThree.points :=
  addEquivOfPrimeCardEq (by simp) muThree_card_points

/-- Inverse Galois automorphisms have the same action on the cube-root group. -/
theorem muThree_inv_smul (σ : Γ) (w : muThree.points) : σ⁻¹ • w = σ • w := by
  rw [muThree_modThreeCyclotomic_smul, muThree_modThreeCyclotomic_smul, map_inv]
  have h : ∀ u : (ZMod 3)ˣ, u⁻¹ = u := by decide
  rw [h]

/-- In additive coordinates, evaluation of a contragredient homomorphism
transforms by the ordinary cube-root action. -/
theorem muThreeCoordinates_contragredient (σ : Γ) (d : muThree.points →+ ZMod 3) :
    muThreeCoordinates (d (σ⁻¹ • muThreeCoordinates 1)) =
      σ • muThreeCoordinates (d (muThreeCoordinates 1)) := by
  rw [muThree_inv_smul, muThree_modThreeCyclotomic_smul, map_nsmul, map_nsmul,
    muThree_modThreeCyclotomic_smul]

/-- Evaluation viewed as a map to the group of all cube roots of unity. -/
def muThreeRootsHom : Multiplicative muThree.points →* rootsOfUnity 3 (AlgebraicClosure ℚ) where
  toFun w := ⟨muThreeUnit w, (mem_rootsOfUnity' 3 _).mpr (muThreeValue_cube w.toAdd)⟩
  map_one' := Subtype.ext muThreeUnit.map_one
  map_mul' w v := Subtype.ext (muThreeUnit.map_mul w v)

/-- Every cube root of unity is the evaluation of an actual cube-root point. -/
theorem muThreeRootsHom_bijective : Function.Bijective muThreeRootsHom := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨fun w v h ↦ muThreeUnit_injective (congrArg Subtype.val h), ?_⟩
  change Nat.card muThree.points = Nat.card (rootsOfUnity 3 (AlgebraicClosure ℚ))
  rw [muThree_card_points, HasEnoughRootsOfUnity.natCard_rootsOfUnity]

/-- An arbitrary cube root of unity has a cube-root point coordinate. -/
theorem exists_muThreeValue_eq (c : AlgebraicClosure ℚ) (hc : c ^ 3 = 1) :
    ∃ w : muThree.points, muThreeValue w = c := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 3 ≠ 0)] at hc
    exact zero_ne_one hc
  let u : rootsOfUnity 3 (AlgebraicClosure ℚ) :=
    ⟨Units.mk0 c hc0, (mem_rootsOfUnity' 3 _).mpr hc⟩
  obtain ⟨w, hw⟩ := muThreeRootsHom_bijective.2 u
  exact ⟨w.toAdd, congrArg (fun v : rootsOfUnity 3 (AlgebraicClosure ℚ) ↦
    ((v : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) hw⟩

end ThreeAdicPlan
