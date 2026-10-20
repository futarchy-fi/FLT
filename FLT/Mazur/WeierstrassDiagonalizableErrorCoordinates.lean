/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassDiagonalizableDefect

/-!
# Full additive coordinates of the original multiplication error

When the reduction of an actual scheme map preserves multiplication, its
entire multiplication defect lies in the square-zero kernel. The original
kernel equivalence extracts its coefficients, and associativity proves the
additive cocycle needed by the integral contraction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableDefect

open DiagonalizableCobar WeierstrassIntegralChart
open WeierstrassDiagonalizableInfinitesimalKernel

universe u
variable {R G : Type u} [CommRing R] [AddCommMonoid G]
  (W : WeierstrassCurve R) (I : Ideal R) (hI : I ^ 2 = ⊥)
  (p : Points W (AddMonoidAlgebra R G))
  (hp : defect W (smoothAlgebraReduction W (coefficientReduction R G I) p) = 1)

/-- Coefficients of the entire original multiplication defect, not a chosen scalar error. -/
def errorCoordinates : G × G →₀ I :=
  ((kernelEquiv W I hI).symm
    ⟨defect W p, (defect_reduction W I p).trans hp⟩).toAdd

/-- Reinserting all coefficients recovers exactly the original group-valued defect. -/
theorem point_errorCoordinates :
    point W I hI (errorCoordinates W I hI p hp) = defect W p :=
  congrArg Subtype.val ((kernelEquiv W I hI).apply_symm_apply _)

/-- Associativity of the actual smooth-group law gives the full additive cocycle. -/
theorem errorCoordinates_cocycle :
    front R I G (errorCoordinates W I hI p hp) +
      leftProduct R I G (errorCoordinates W I hI p hp) =
    back R I G (errorCoordinates W I hI p hp) +
      rightProduct R I G (errorCoordinates W I hI p hp) := by
  apply point_injective W I hI
  rw [point_add, point_add, ← point_front, ← point_leftProduct,
    ← point_back, ← point_rightProduct, point_errorCoordinates]
  exact defect_cocycle W p

/-- The full error is the coboundary of its extracted last-trivial-character coefficient. -/
theorem errorCoordinates_boundary :
    errorCoordinates W I hI p hp =
      boundary R I G (contract R I G (errorCoordinates W I hI p hp)) :=
  cocycle_eq_boundary R I G _ (errorCoordinates_cocycle W I hI p hp)

/-- The original scheme-map error determines a unique ideal-valued correction. -/
theorem errorCoordinates_unique_correction :
    ∃! q : G →₀ I, boundary R I G q = errorCoordinates W I hI p hp :=
  existsUnique_correction R I G _ (errorCoordinates_cocycle W I hI p hp)

end FLT.Mazur.WeierstrassDiagonalizableDefect
