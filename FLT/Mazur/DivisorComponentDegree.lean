/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteDivisorCohomology
public import FLT.Mazur.FiniteDivisorComponentAvoidance
public import FLT.Mazur.CartierIdealPullbackComparison

/-!
# Component degrees of a finite effective Cartier divisor

On a proper pure one-dimensional scheme, the pullback of O(D) to a reduced
irreducible component is the line of the restricted divisor. Its degree is
the actual restricted length and is positive exactly when the component
meets the original divisor support.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open CoherentDevissage

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ f)]
  (hX : CurveFiberHypotheses.PureDimensionOne X)

include hX

/-- The degree of the actual pulled-back line equals the component divisor length. -/
theorem divisor_component_degree_eq_length (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    let C : Closeds X := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
    curveSheafDegree (reducedClosedSubschemeι C ≫ f)
      ((pullback (reducedClosedSubschemeι C)).obj (divisorLineBundle I hI)) =
        (reducedComponentDivisorLength f I C : ℤ) := by
  let C : Closeds X := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  let i := reducedClosedSubschemeι C
  have hJ := finiteDivisor_cartier_on_component f hI hX Z hZ
  have := divisor_comap_isFinite f I i
  exact (curveSheafDegree_iso (i ≫ f) (divisorLinePullbackIsoOfCartier i hI hJ)).trans
    (divisor_degree_eq_fieldLength (i ≫ f) hJ)

/-- Positive component degree is exactly intersection with the actual support. -/
theorem divisor_component_degree_pos_iff (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    let C : Closeds X := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
    0 < curveSheafDegree (reducedClosedSubschemeι C ≫ f)
      ((pullback (reducedClosedSubschemeι C)).obj (divisorLineBundle I hI)) ↔
        ((I.support : Set X) ∩ Z).Nonempty := by
  dsimp only
  rw [divisor_component_degree_eq_length f hI hX Z hZ]
  exact (Int.natCast_pos).trans (reducedComponentDivisorLength_pos_iff f I _)

/-- Meeting every component is equivalent to positive degree on every reduced component. -/
theorem divisor_all_component_degrees_pos_iff :
    (∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X),
      0 < curveSheafDegree (reducedClosedSubschemeι
        ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩ ≫ f)
        ((pullback (reducedClosedSubschemeι
          ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩)).obj (divisorLineBundle I hI))) ↔
      ∀ Z ∈ irreducibleComponents X, ((I.support : Set X) ∩ Z).Nonempty := by
  exact forall₂_congr fun Z hZ ↦ divisor_component_degree_pos_iff f hI hX Z hZ

end FLT.Mazur.FCurve
