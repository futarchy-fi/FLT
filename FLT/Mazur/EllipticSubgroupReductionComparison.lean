/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupReducedSections
public import FLT.Mazur.EllipticGoodComponent

/-!
# Smooth reduction detects equality of actual closure specializations

The ambient closed immersion compares equality of residue evaluations with
equality under the original smooth reduction homomorphism. In good reduction
all original subgroup points have the required smooth reductions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- Smooth projective reduction agrees exactly with equality of closure residue evaluations. -/
theorem globalClosureSpecializedEvaluation_eq_iff (P Q : H)
    (hP : SmoothReduction A W P.1) (hQ : SmoothReduction A W Q.1) :
    globalClosureSpecializedEvaluation A W H (ResidueField A) P =
        globalClosureSpecializedEvaluation A W H (ResidueField A) Q ↔
      smoothReductionHom A W ⟨P.1, hP⟩ = smoothReductionHom A W ⟨Q.1, hQ⟩ := by
  constructor
  · intro h
    apply projectiveToIntegral_injective W
    apply Over.OverMorphism.ext
    rw [← globalClosureSpecializedEvaluation_smoothReduction A W H P hP,
      ← globalClosureSpecializedEvaluation_smoothReduction A W H Q hQ, h]
  · intro h
    have he := congrArg (fun P => (projectiveToIntegral W P).left) h
    rw [← globalClosureSpecializedEvaluation_smoothReduction A W H P hP,
      ← globalClosureSpecializedEvaluation_smoothReduction A W H Q hQ] at he
    simp only [← Category.assoc] at he
    have hc := (cancel_mono (closureToCurve A W H 1 2)).mp he
    have hs := (cancel_mono (gluedClosure A W H 1 2).isoSpec.inv).mp hc
    exact AlgHom.coe_ringHom_injective
      (congrArg CommRingCat.Hom.hom (Spec.map_injective hs))

omit [Finite H] in
/-- Unit discriminant puts every original subgroup point in the smooth-reduction subgroup. -/
theorem subgroup_le_ellipticE0_of_unit_discriminant (hΔ : IsUnit W.Δ) :
    H ≤ ellipticE0 A W := by
  let : W.IsElliptic := ⟨hΔ⟩
  intro P _
  exact smoothReduction_of_isElliptic A W P

/-- The actual smooth reduction restricted to a subgroup with smooth reduction. -/
def subgroupSmoothReduction (hH : H ≤ ellipticE0 A W) :
    H →+ (W.map (residue A)).toProjective.Point :=
  (smoothReductionHom A W).comp (AddSubgroup.inclusion hH)

/-- Equality of closure specializations is equality of the restricted reduction homomorphism. -/
theorem subgroupSmoothReduction_eq_iff (hH : H ≤ ellipticE0 A W) (P Q : H) :
    subgroupSmoothReduction A W H hH P = subgroupSmoothReduction A W H hH Q ↔
      globalClosureSpecializedEvaluation A W H (ResidueField A) P =
        globalClosureSpecializedEvaluation A W H (ResidueField A) Q :=
  (globalClosureSpecializedEvaluation_eq_iff A W H P Q (hH P.2) (hH Q.2)).symm

end FLT.Mazur.EllipticSubgroupChart
