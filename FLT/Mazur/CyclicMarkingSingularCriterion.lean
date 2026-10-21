/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularSubgroup

/-!
# The exact subgroup criterion for singular cyclic orbit divisors

An actual subgroup with the prescribed whole-curve ideal forces the smooth-group
multiplication equation. Together with the construction, this gives an exact
criterion and reconstructs original Cartier-generated subgroups without
universal distinctness or invertibility assumptions on the degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- Restricting a subgroup's whole-curve ideal recovers its smooth-group closed ideal. -/
theorem FiniteSubgroup.inclusion_ker_eq_restriction (H : E.FiniteSubgroup n) :
    H.inclusion.left.ker = H.ideal.comap E.inclusion.left := by
  have hp : IsPullback H.inclusion.left (𝟙 _) E.inclusion.left H.curveMap.left :=
    IsPullback.of_vert_isIso_mono ⟨by simp [FiniteSubgroup.curveMap]⟩
  rw [FiniteSubgroup.ideal, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso hp.isoPullback.hom, hp.isoPullback_hom_fst]

/-- An original subgroup with the orbit ideal forces the actual multiplication equation. -/
theorem cyclicMarkingGroupIdeal_multiplication_of_subgroup (H : E.FiniteSubgroup n)
    (hH : H.ideal = E.cyclicMarkingIdeal φ) :
    ClosedGroupIdeal.multiplicationEquation E.group (E.cyclicMarkingGroupIdeal φ) = 0 := by
  have hi : E.cyclicMarkingGroupIdeal φ = H.inclusion.left.ker := by
    rw [cyclicMarkingGroupIdeal_eq_comap, ← hH, H.inclusion_ker_eq_restriction E]
  rw [hi]
  let e : H.carrier ≅ ClosedGroupIdeal.carrier E.group H.inclusion.left.ker :=
    Over.isoMk (asIso H.inclusion.left.toImage) (by
      change H.inclusion.left.toImage ≫ H.inclusion.left.imageι ≫ E.group.hom = _
      rw [Scheme.Hom.toImage_imageι_assoc, H.inclusion.w])
  apply ClosedGroupIdeal.multiplicationEquation_of_group E.group H.inclusion.left.ker
    H.inclusion e
  apply Over.OverMorphism.ext
  exact H.inclusion.left.toImage_imageι

variable [NeZero n] [SmoothOfRelativeDimension 1 E.group.hom]

/-- The multiplication equation is exactly the finite-subgroup condition on the orbit ideal. -/
theorem singularCyclicDivisorMultiplication_iff_subgroup :
    ClosedGroupIdeal.multiplicationEquation E.group (E.cyclicMarkingGroupIdeal φ) = 0 ↔
      ∃ H : E.FiniteSubgroup n, H.ideal = E.cyclicMarkingIdeal φ := by
  constructor
  · intro hm
    exact ⟨E.singularCyclicDivisorSubgroup φ hm, E.singularCyclicDivisorSubgroup_ideal φ hm⟩
  · rintro ⟨H, hH⟩
    exact E.cyclicMarkingGroupIdeal_multiplication_of_subgroup φ H hH

variable (H : E.FiniteSubgroup n) {P : 𝟙_ (Over S) ⟶ H.carrier}
  (hP : H.IsCartierGenerator P)

omit [SmoothOfRelativeDimension 1 E.group.hom] in
/-- The original Cartier generator satisfies the singular orbit multiplication equation. -/
theorem FiniteSubgroup.generatorMarking_singularMultiplication :
    ClosedGroupIdeal.multiplicationEquation E.group
      (E.cyclicMarkingGroupIdeal (H.generatorCurveMarking hP)) = 0 :=
  E.cyclicMarkingGroupIdeal_multiplication_of_subgroup (H.generatorCurveMarking hP) H
    (H.generatorCurveMarking_ideal E hP).symm

/-- The singular orbit construction recovers the entire original Cartier-generated subgroup. -/
def FiniteSubgroup.generatorMarkingSingularCompatibleIso :
    FiniteSubgroup.CompatibleIso
      (E.singularCyclicDivisorSubgroup (H.generatorCurveMarking hP)
        (H.generatorMarking_singularMultiplication E hP)) H :=
  E.singularCyclicDivisorOriginalIso (H.generatorCurveMarking hP)
    (H.generatorMarking_singularMultiplication E hP) H (H.generatorCurveMarking_ideal E hP).symm

end FLT.Mazur.GeneralizedEllipticCurve
