/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisTupleSchemeComparison

/-!
# Intrinsic classifying morphisms on the intersection of basis loci

The actual intersection of the two basis opens maps into the chart transition
domain. Its two intrinsic parameters agree after the change of tuple.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]

/-- The common intrinsic basis open of the actual quotient family. -/
def polynomialBasisIntersection : (Spec (.of S)).Opens :=
  polynomialBasisOpen R I d w S J ⊓ polynomialBasisOpen R I d v S J

/-- The two inclusions of the common intrinsic locus have the same map to the base. -/
theorem polynomialBasisIntersection_over :
    (Spec (.of S)).homOfLE (U := polynomialBasisIntersection R I d w v S J) inf_le_left ≫
      Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J) =
    (Spec (.of S)).homOfLE (U := polynomialBasisIntersection R I d w v S J) inf_le_right ≫
      Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d v S J) := by
  simp only [Scheme.homOfLE_ι]

variable [Module.Flat S (MvPolynomial I S ⧸ J)]

/-- The common intrinsic locus maps to the actual transition domain. -/
def intrinsicBasisIntersectionMorphism :
    (polynomialBasisIntersection R I d w v S J).toScheme ⟶
      (chartTupleTransitionOpen R I d w v).toScheme :=
  intrinsicTupleComparison R I d w v S J
    ((Spec (.of S)).homOfLE inf_le_left) ((Spec (.of S)).homOfLE inf_le_right)
    (polynomialBasisIntersection_over R I d w v S J)

/-- The overlap map recovers the restriction of the first intrinsic classifying morphism. -/
theorem intrinsicBasisIntersectionMorphism_ι :
    intrinsicBasisIntersectionMorphism R I d w v S J ≫
      (chartTupleTransitionOpen R I d w v).ι =
    (Spec (.of S)).homOfLE inf_le_left ≫ intrinsicChartMorphism R I d w S J :=
  intrinsicTupleComparison_ι R I d w v S J _ _ _

/-- On the actual intersection, changing tuple identifies the two glued classifying morphisms. -/
theorem intrinsicBasisIntersectionMorphism_transition :
    intrinsicBasisIntersectionMorphism R I d w v S J ≫ chartTupleTransition R I d w v =
    (Spec (.of S)).homOfLE inf_le_right ≫ intrinsicChartMorphism R I d v S J :=
  intrinsicTupleComparison_transition R I d w v S J _ _ _

end FLT.Mazur.HilbertChart
