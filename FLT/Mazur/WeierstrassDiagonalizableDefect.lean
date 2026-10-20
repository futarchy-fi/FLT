/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableCofaceIdentities
public import FLT.Mazur.WeierstrassDiagonalizableKernelNaturality

/-!
# The multiplication defect of an actual smooth-group scheme map

For any map from a diagonalizable test scheme into the original smooth curve,
the discrepancy between the two multiplication maps is an actual smooth-group
point on the product. Associativity gives its full cocycle identity.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableDefect

open DiagonalizableCobar WeierstrassIntegralChart

universe u
variable {R G : Type u} [CommRing R] [AddCommMonoid G] (W : WeierstrassCurve R)

/-- Actual points of the original relative smooth group over a coefficient algebra. -/
abbrev Points (A : Type u) [CommRing A] [Algebra R A] :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ (integralSmoothGroup W).X

/-- The actual discrepancy between the two full multiplication maps. -/
def defect {S : Type u} [CommRing S] [Algebra R S]
    (p : Points W (AddMonoidAlgebra S G)) : Points W (AddMonoidAlgebra S (G × G)) :=
  smoothAlgebraReduction W ((firstMap S G).restrictScalars R) p *
    smoothAlgebraReduction W ((secondMap S G).restrictScalars R) p /
      smoothAlgebraReduction W ((diagonalMap S G).restrictScalars R) p

/-- Over the original base the defect uses exactly the original character maps. -/
theorem defect_base (p : Points W (AddMonoidAlgebra R G)) :
    defect W p = smoothAlgebraReduction W (firstMap R G) p *
      smoothAlgebraReduction W (secondMap R G) p /
        smoothAlgebraReduction W (diagonalMap R G) p := rfl

private theorem cocycle_cancel {A : Type*} [CommGroup A] (a b c d e f : A) :
    (a * b / d) * (d * c / e) = (b * c / f) * (a * f / e) := by
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, _root_.mul_assoc]

/-- Associativity gives the full group-valued cocycle, before choosing any coordinates. -/
theorem defect_cocycle (p : Points W (AddMonoidAlgebra R G)) :
    smoothAlgebraReduction W (frontMap R G) (defect W p) *
      smoothAlgebraReduction W (leftProductMap R G) (defect W p) =
    smoothAlgebraReduction W (backMap R G) (defect W p) *
      smoothAlgebraReduction W (rightProductMap R G) (defect W p) := by
  simp only [defect_base, map_div, map_mul, ← smoothAlgebraReduction_comp,
    front_first_comp, front_second_comp, front_diagonal_comp,
    leftProduct_second_comp, leftProduct_diagonal_comp, back_diagonal_comp]
  exact cocycle_cancel _ _ _ _ _ _

/-- Base reduction commutes with every character restriction on actual smooth points. -/
theorem restriction_reduction {H : Type u} [AddCommMonoid H] (I : Ideal R)
    (f : G →+ H) (p : Points W (AddMonoidAlgebra R G)) :
    smoothAlgebraReduction W (coefficientReduction R H I)
      (smoothAlgebraReduction W (AddMonoidAlgebra.mapDomainAlgHom R R f) p) =
    smoothAlgebraReduction W (AddMonoidAlgebra.mapDomainAlgHom R (R ⧸ I) f)
      (smoothAlgebraReduction W (coefficientReduction R G I) p) := by
  rw [← smoothAlgebraReduction_comp, coefficientReduction_mapDomain_comp,
    smoothAlgebraReduction_comp]

/-- The entire original multiplication error reduces to the error of the reduced map. -/
theorem defect_reduction (I : Ideal R) (p : Points W (AddMonoidAlgebra R G)) :
    smoothAlgebraReduction W (coefficientReduction R (G × G) I) (defect W p) =
      defect W (smoothAlgebraReduction W (coefficientReduction R G I) p) := by
  rw [defect_base, map_div, map_mul]
  simp only [firstMap, secondMap, diagonalMap]
  rw [restriction_reduction, restriction_reduction, restriction_reduction]
  rfl

end FLT.Mazur.WeierstrassDiagonalizableDefect
