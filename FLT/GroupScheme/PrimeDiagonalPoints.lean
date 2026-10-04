/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DiagonalGroupModel
public import FLT.GroupScheme.RootModuleLinear

/-!
# Prime cyclic diagonalizable points

A primitive root gives all geometric points of the integral cyclic group
algebra. The chosen coordinates intertwine its actual cyclotomic action.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open KummerTheory
namespace ThreeAdicPlan

variable (R K : Type) [CommRing R] [Field K] [Algebra R K] [CharZero K]
  {p : ℕ} [Fact p.Prime] {ζ : (AlgebraicClosure K)ˣ} (hζ : IsPrimitiveRoot ζ p)

/-- The character of the cyclic degree group specified by a prime-field coordinate. -/
def primeDiagonalCharacter (x : ZMod p) : Multiplicative (ZMod p) →* AlgebraicClosure K where
  toFun a := rootUnit (primeRootCoordinates hζ (x * a.toAdd))
  map_one' := by simp
  map_mul' a b := by simp [mul_add, map_add]

/-- The corresponding actual geometric point of the integral diagonalizable model. -/
def primeDiagonalPoint (x : ZMod p) : (diagonalGroupModel R K (ZMod p)).Points :=
  diagonalGroupPoint R K (ZMod p) (primeDiagonalCharacter K hζ x)

/-- The value of a group-like generator is the prescribed root power. -/
theorem primeDiagonalPoint_single (x a : ZMod p) :
    (diagonalGroupModel R K (ZMod p)).integralPoints (primeDiagonalPoint R K hζ x)
      (MonoidAlgebra.single (Multiplicative.ofAdd a) 1) =
        (rootUnit (primeRootCoordinates hζ (x * a)) : AlgebraicClosure K) :=
  diagonalGroupPoint_single R K (ZMod p) _ _

/-- The root-coordinate points preserve addition. -/
theorem primeDiagonalPoint_add (x y : ZMod p) :
    primeDiagonalPoint R K hζ (x + y) =
      primeDiagonalPoint R K hζ x + primeDiagonalPoint R K hζ y := by
  unfold primeDiagonalPoint
  rw [← diagonalGroupPoint_mul]
  congr 1
  ext a
  simp [primeDiagonalCharacter, add_mul, map_add]

/-- The explicit points exhaust the geometric generic fibre, without a cardinality assumption. -/
theorem primeDiagonalPoint_bijective : Function.Bijective (primeDiagonalPoint R K hζ) := by
  constructor
  · intro x y h
    have he := congrArg (fun w ↦ (diagonalGroupModel R K (ZMod p)).integralPoints w
      (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod p)) 1)) h
    simp only [primeDiagonalPoint_single, mul_one] at he
    exact (primeRootCoordinates hζ).injective (rootUnit_injective (Units.ext he))
  · intro w
    obtain ⟨χ, rfl⟩ := (diagonalGroupPointEquiv R K (ZMod p)).surjective w
    let u := χ.toHomUnits (Multiplicative.ofAdd (1 : ZMod p))
    have hu : u ^ p = 1 := by
      change χ.toHomUnits (Multiplicative.ofAdd (1 : ZMod p)) ^ p = 1
      rw [← map_pow]
      simp [← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero]
    let z : RootModule (AlgebraicClosure K) p := Additive.ofMul ⟨u, hu⟩
    obtain ⟨x, hx⟩ := (primeRootCoordinates hζ).surjective z
    refine ⟨x, ?_⟩
    change diagonalGroupPoint R K (ZMod p) _ = diagonalGroupPoint R K (ZMod p) χ
    congr 1
    apply MonoidHom.ext
    intro a
    have ha : (Multiplicative.ofAdd (1 : ZMod p)) ^ a.toAdd.val = a := by
      simp [← ofAdd_nsmul, nsmul_eq_mul]
    change (rootUnit (primeRootCoordinates hζ (x * a.toAdd)) : AlgebraicClosure K) = χ a
    rw [mul_comm, primeRootCoordinates_mul, hx]
    change ((u ^ a.toAdd.val : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = χ a
    change χ (Multiplicative.ofAdd (1 : ZMod p)) ^ a.toAdd.val = χ a
    rw [← map_pow, ha]

/-- Prime coordinates with cyclotomic action map equivariantly to the actual points. -/
theorem primeDiagonalPoint_equivariant (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : ZMod p) :
    primeDiagonalPoint R K hζ ((primeCyclotomicCharacter hζ g : ZMod p) * x) =
      g • primeDiagonalPoint R K hζ x := by
  unfold primeDiagonalPoint
  rw [diagonalGroupPoint_smul]
  congr 1
  apply MonoidHom.ext
  intro a
  change (rootUnit (primeRootCoordinates hζ
    (((primeCyclotomicCharacter hζ g : ZMod p) * x) * a.toAdd)) : AlgebraicClosure K) =
    g (rootUnit (primeRootCoordinates hζ (x * a.toAdd)))
  rw [mul_assoc]
  exact congrArg (fun z : RootModule (AlgebraicClosure K) p ↦ (rootUnit z : AlgebraicClosure K))
    (primeCyclotomicCoordinates_equivariant hζ g (x * a.toAdd))

end ThreeAdicPlan
