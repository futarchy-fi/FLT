/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationNegation
public import FLT.Mazur.WeierstrassDividedTangentBranchSource

/-!
# Complementary strict-branch inputs by actual divided negation

Negating both original inputs converts the first ordinate into the strict
branch factor. The tangent denominator becomes the negative reversed
denominator, so the complementary domain is explicit over every ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)

/-- The actual negative input in the unchanged divided coordinate algebra. -/
def branchNegativeInput : Coordinate W s b3 b4 b6 →ₐ[R] S :=
  a.comp (negation W s b3 b4 b6)

/-- The negative input retains its original divided abscissa. -/
theorem branchNegativeInput_x :
    branchNegativeInput W s b3 b4 b6 a (x W s b3 b4 b6) = a (x W s b3 b4 b6) := by
  simp only [branchNegativeInput, AlgHom.comp_apply, negation_x]

/-- The negative input has the full original divided negation formula. -/
theorem branchNegativeInput_y :
    branchNegativeInput W s b3 b4 b6 a (y W s b3 b4 b6) =
      -a (y W s b3 b4 b6) - algebraMap R S W.a₁ * a (x W s b3 b4 b6) -
        algebraMap R S b3 := by
  simp only [branchNegativeInput, AlgHom.comp_apply, negation_y,
    map_sub, map_neg, map_mul, AlgHom.commutes]

local notation "a'" => branchNegativeInput W s b3 b4 b6 a
local notation "c'" => branchNegativeInput W s b3 b4 b6 c

/-- The strict-branch factor on negative inputs is the negative original first ordinate. -/
theorem branchNegativeInput_factor :
    dividedTangentBranchFactor W s b3 b4 b6 a' = -a (y W s b3 b4 b6) := by
  simp only [dividedTangentBranchFactor, branchNegativeInput_x, branchNegativeInput_y]
  ring

/-- The negative inputs use the exact reversed original tangent open. -/
theorem branchNegativeInput_denominator :
    dividedTangentDenominator W s b3 b4 b6 a' c' =
      -dividedTangentDenominator W s b3 b4 b6 c a := by
  simp only [dividedTangentDenominator, branchNegativeInput_x, branchNegativeInput_y]
  ring

/-- The complementary branch principal open is determined by original coordinates alone. -/
theorem branchNegativeInput_branchProduct :
    dividedTangentDenominator W s b3 b4 b6 a' c' *
        dividedTangentBranchFactor W s b3 b4 b6 a' =
      dividedTangentDenominator W s b3 b4 b6 c a * a (y W s b3 b4 b6) := by
  rw [branchNegativeInput_denominator, branchNegativeInput_factor, neg_mul_neg]

/-- Applying the constructed negative twice recovers the entire original input map. -/
theorem branchNegativeInput_involutive :
    branchNegativeInput W s b3 b4 b6 a' = a := by
  rw [branchNegativeInput, branchNegativeInput, AlgHom.comp_assoc, negation_comp,
    AlgHom.comp_id]

end FLT.Mazur.WeierstrassDilatation
