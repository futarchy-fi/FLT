/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DiagonalGroupModel
public import FLT.GroupScheme.PrimeDualCharacters

/-!
# Diagonalizable points for arbitrary finite prime-field modules

Evaluation on the linear dual constructs all geometric points and recovers
exactly the scalar cyclotomic action, independently of a basis or trace pairing.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open KummerTheory
namespace ThreeAdicPlan

variable (R K V : Type) [CommRing R] [Field K] [Algebra R K] [CharZero K]
  {p : ℕ} [Fact p.Prime] [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  {ζ : (AlgebraicClosure K)ˣ} (hζ : IsPrimitiveRoot ζ p)

local instance : Finite (Module.Dual (ZMod p) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- Evaluation on the dual gives an actual point of the integral group algebra. -/
def finiteDiagonalPoint (x : V) :
    (diagonalGroupModel R K (Module.Dual (ZMod p) V)).Points :=
  diagonalGroupPoint R K _
    (primeDualCharacter hζ _ (Module.Dual.eval (ZMod p) V x))

/-- The point evaluation is the specified primitive root raised to the functional's value. -/
theorem finiteDiagonalPoint_single (x : V) (a : Module.Dual (ZMod p) V) :
    (diagonalGroupModel R K (Module.Dual (ZMod p) V)).integralPoints
      (finiteDiagonalPoint R K V hζ x) (MonoidAlgebra.single (Multiplicative.ofAdd a) 1) =
      (rootUnit (primeRootCoordinates hζ (a x)) : AlgebraicClosure K) :=
  diagonalGroupPoint_single R K _ _ _

/-- Evaluation preserves addition of the original coefficient vectors. -/
theorem finiteDiagonalPoint_add (x y : V) :
    finiteDiagonalPoint R K V hζ (x + y) =
      finiteDiagonalPoint R K V hζ x + finiteDiagonalPoint R K V hζ y := by
  unfold finiteDiagonalPoint
  rw [← diagonalGroupPoint_mul]
  congr 1
  ext a
  simp [primeDualCharacter, map_add]

/-- Duality exhausts the geometric points; no point-counting premise is needed. -/
theorem finiteDiagonalPoint_bijective : Function.Bijective (finiteDiagonalPoint R K V hζ) :=
  (diagonalGroupPointEquiv R K _).bijective.comp
    ((primeDualCharacterEquiv hζ _).bijective.comp (Module.evalEquiv (ZMod p) V).bijective)

/-- The actual Galois action agrees with prime cyclotomic scalar multiplication. -/
theorem finiteDiagonalPoint_equivariant (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : V) :
    finiteDiagonalPoint R K V hζ ((primeCyclotomicCharacter hζ g : ZMod p) • x) =
      g • finiteDiagonalPoint R K V hζ x := by
  unfold finiteDiagonalPoint
  rw [diagonalGroupPoint_smul]
  congr 1
  ext a
  change (rootUnit (primeRootCoordinates hζ
    (a ((primeCyclotomicCharacter hζ g : ZMod p) • x))) : AlgebraicClosure K) =
    g (rootUnit (primeRootCoordinates hζ (a x)))
  rw [map_smul]
  exact congrArg (fun z : RootModule (AlgebraicClosure K) p ↦ (rootUnit z : AlgebraicClosure K))
    (primeCyclotomicCoordinates_equivariant hζ g (a x))

end ThreeAdicPlan
