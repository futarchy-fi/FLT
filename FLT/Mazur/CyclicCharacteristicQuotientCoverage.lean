/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicQuotientGluing
public import FLT.Mazur.CyclicCharacteristicInvariantAffineCoverage

/-!
# Smooth subgroup coverage through the single constructed quotient

Every original smooth cyclic subgroup object has an fppf local parameter in
the existing finite affine family, hence a map into the single quotient.
The original source lifts retain the full curve and subgroup comparisons.
This does not assert that a universal curve descends to the coarse quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The original affine parameter chart maps into the actual single quotient. -/
def invariantAffineToDisjointQuotient (i : InvariantAffineIndex n) :
    invariantAffineChart n i ⟶ normalizedDisjointQuotient n :=
  invariantAffineQuotientMap n i ≫ disjointAffineQuotientInclusion n i

/-- This map is the restriction of the single quotient map on the original source. -/
@[reassoc] theorem invariantAffineToDisjointQuotient_eq (i : InvariantAffineIndex n) :
    invariantAffineToDisjointQuotient n i =
      disjointAffineInclusion n i ≫ normalizedDisjointQuotientMap n :=
  disjointAffineQuotientMap_inclusion n i

/-- Original relabelings preserve the actual map into the assembled quotient. -/
@[reassoc] theorem invariantAffineToDisjointQuotient_invariant (i : InvariantAffineIndex n)
    (g : RelabelGroup n) :
    (invariantAffineAction n i g).hom ≫ invariantAffineToDisjointQuotient n i =
      invariantAffineToDisjointQuotient n i := by
  rw [invariantAffineToDisjointQuotient_eq, disjointAffineAction_inclusion_assoc,
    normalizedDisjointQuotientMap_invariant]

variable {S : Scheme} {E : GeneralizedEllipticCurve S} [Smooth E.curve.hom]
  (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)

include hc ha in
/-- Smooth cyclic objects have actual local quotient parameters with original subgroup lifts. -/
theorem exists_disjointQuotient_subgroup_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (i : C.I₀ → InvariantAffineIndex n)
      (q : ∀ a : C.I₀, C.X a ⟶ invariantAffineChart n (i a))
      (v : ∀ a : C.I₀, C.X a ⟶ normalizedDisjointQuotient n),
      (∀ a, v a = q a ≫ invariantAffineToDisjointQuotient n (i a)) ∧
      (∀ a, v a = (q a ≫ disjointAffineInclusion n (i a)) ≫
        normalizedDisjointQuotientMap n) ∧
      ∀ a, Nonempty (CompatibleIso ((invariantAffineSubgroup n (i a)).baseChange (q a))
        (H.baseChange (C.f a))) := by
  obtain ⟨C, i, q, hq⟩ := exists_invariantAffine_subgroup_fppf_cover n H hc ha
  refine ⟨C, i, q, fun a => q a ≫ invariantAffineToDisjointQuotient n (i a),
    fun _ => rfl, ?_, hq⟩
  intro a
  simp only [invariantAffineToDisjointQuotient_eq, Category.assoc]

end FLT.Mazur.CyclicCharacteristicAtlas
