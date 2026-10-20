/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassDiagonalizableErrorCoordinates

/-!
# Correcting the original smooth-group scheme map

The explicit integral contraction removes the entire multiplication defect of
an actual map whose reduction preserves multiplication. The correction is an
actual smooth-group point and leaves the specified reduction unchanged.
No subgroup-order inverse or replacement of the original ideal is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableDefect

open DiagonalizableCobar WeierstrassIntegralChart
open WeierstrassDiagonalizableInfinitesimalKernel

universe u
variable {R G : Type u} [CommRing R] [AddCommMonoid G] (W : WeierstrassCurve R)

/-- The full multiplication defect is a homomorphism between the actual point groups. -/
def defectHom : Points W (AddMonoidAlgebra R G) →*
    Points W (AddMonoidAlgebra R (G × G)) :=
  (smoothAlgebraReduction W (firstMap R G) *
    smoothAlgebraReduction W (secondMap R G)) / smoothAlgebraReduction W (diagonalMap R G)

/-- Dividing original scheme maps divides their full multiplication defects. -/
theorem defect_div (p q : Points W (AddMonoidAlgebra R G)) :
    defect W (p / q) = defect W p / defect W q := (defectHom W).map_div p q

variable (I : Ideal R) (hI : I ^ 2 = ⊥)

/-- The defect of an inserted kernel point is its full additive coboundary. -/
theorem defect_point (q : G →₀ I) :
    defect W (point W I hI q) = point W I hI (boundary R I G q) := by
  rw [defect_base, point_first, point_second, point_diagonal, ← point_add, ← point_sub]
  rfl

variable (p : Points W (AddMonoidAlgebra R G))
  (hp : defect W (smoothAlgebraReduction W (coefficientReduction R G I) p) = 1)

/-- The actual corrected map on the original diagonalizable test scheme. -/
def corrected : Points W (AddMonoidAlgebra R G) :=
  p / point W I hI (contract R I G (errorCoordinates W I hI p hp))

/-- The complete original multiplication defect is cancelled exactly. -/
theorem corrected_defect : defect W (corrected W I hI p hp) = 1 := by
  rw [corrected, defect_div, defect_point, ← errorCoordinates_boundary,
    point_errorCoordinates, div_self']

/-- The corrected map retains the prescribed reduction on the entire original base fiber. -/
theorem corrected_reduction :
    smoothAlgebraReduction W (coefficientReduction R G I) (corrected W I hI p hp) =
      smoothAlgebraReduction W (coefficientReduction R G I) p := by
  rw [corrected, map_div, point_reduction, div_one]

/-- The corrected original scheme map preserves the full group multiplication. -/
theorem corrected_multiplication :
    smoothAlgebraReduction W (firstMap R G) (corrected W I hI p hp) *
      smoothAlgebraReduction W (secondMap R G) (corrected W I hI p hp) =
    smoothAlgebraReduction W (diagonalMap R G) (corrected W I hI p hp) :=
  div_eq_one.mp (corrected_defect W I hI p hp)

include hI hp in
/-- Every underlying scheme lift of a multiplicative map admits an actual correction. -/
theorem exists_corrected : ∃ q : Points W (AddMonoidAlgebra R G),
    smoothAlgebraReduction W (coefficientReduction R G I) q =
      smoothAlgebraReduction W (coefficientReduction R G I) p ∧ defect W q = 1 :=
  ⟨corrected W I hI p hp, corrected_reduction W I hI p hp, corrected_defect W I hI p hp⟩

end FLT.Mazur.WeierstrassDiagonalizableDefect
