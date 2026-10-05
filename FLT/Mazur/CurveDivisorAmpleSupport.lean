/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffineBase
public import FLT.Mazur.CurveComponentAmpleCriterion
public import FLT.Mazur.DivisorComponentDegree
public import FLT.Mazur.ProperAmpleConverse

/-!
# Ampleness of finite divisors detected by component support

For a proper pure one-dimensional scheme, a finite effective Cartier divisor
is ample exactly when it meets every irreducible component. The same criterion
holds for the project's closed-projective-power predicate. On an integral
curve the condition reduces to nonempty divisor support.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

namespace FLT.Mazur.FCurve
open CoherentDevissage

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ f)]

include f

/-- The support criterion for a finite Cartier divisor on a proper pure curve. -/
theorem divisor_ample_iff_meets_components (hX : CurveFiberHypotheses.PureDimensionOne X) :
    AmpleLineBundle (divisorLineBundle I hI) ↔
      ∀ Z ∈ irreducibleComponents X, ((I.support : Set X) ∩ Z).Nonempty := by
  rw [ampleLineBundle_iff_on_irreducibleComponents f hI.divisorLineBundle_locallyFreeRankOne]
  constructor
  · intro h Z hZ
    let C : Closeds X := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
    let : IsIntegral (reducedClosedSubscheme C) := reducedClosedSubscheme_isIntegral C hZ.1
    exact (divisor_component_degree_pos_iff f hI hX Z hZ).mp
      ((h C hZ).curveSheafDegree_pos (reducedClosedSubschemeι C ≫ f) (hX Z hZ))
  · intro h C hC
    let : IsIntegral (reducedClosedSubscheme C) := reducedClosedSubscheme_isIntegral C hC.1
    apply (ampleLineBundle_iff_curveSheafDegree_pos (reducedClosedSubschemeι C ≫ f)
      (hX C hC) (hI.divisorLineBundle_locallyFreeRankOne.pullback _)).mpr
    exact (divisor_component_degree_pos_iff f hI hX C hC).mpr (h C hC)

/-- Closed projective powers obey the same component-support criterion. -/
theorem divisor_relativeAmple_iff_meets_components
    (hX : CurveFiberHypotheses.PureDimensionOne X) :
    RelativeAmple f (divisorLineBundle I hI) ↔
      ∀ Z ∈ irreducibleComponents X, ((I.support : Set X) ∩ Z).Nonempty := by
  rw [relativeAmple_iff_relativelyAmpleLineBundle hI.divisorLineBundle_locallyFreeRankOne,
    relativelyAmpleLineBundle_iff_of_affine f, divisor_ample_iff_meets_components f hI hX]

/-- A finite Cartier divisor on a proper integral curve is ample exactly when it is nonempty. -/
theorem divisor_ample_iff_nonempty [IsIntegral X] (hd : topologicalKrullDim X = 1) :
    AmpleLineBundle (divisorLineBundle I hI) ↔ (I.support : Set X).Nonempty := by
  rw [ampleLineBundle_iff_curveSheafDegree_pos f hd hI.divisorLineBundle_locallyFreeRankOne,
    divisor_degree_eq_fieldLength f hI]
  exact Int.natCast_pos.trans (divisorFieldLength_pos_iff f I)

/-- A nonempty finite divisor on an integral curve has a closed very ample positive power. -/
theorem divisor_relativeAmple_iff_nonempty [IsIntegral X] (hd : topologicalKrullDim X = 1) :
    RelativeAmple f (divisorLineBundle I hI) ↔ (I.support : Set X).Nonempty := by
  rw [relativeAmple_iff_relativelyAmpleLineBundle hI.divisorLineBundle_locallyFreeRankOne,
    relativelyAmpleLineBundle_iff_of_affine f, divisor_ample_iff_nonempty f hI hd]

end FLT.Mazur.FCurve
