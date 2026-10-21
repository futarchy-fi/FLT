/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedAmpleMarking

/-!
# Full marked coverage by the unrestricted ample chart

The original generator cover supplies ample chart tests with their complete
curve and subgroup comparisons, both independent auxiliary factors, and the
prescribed Cartier generator. No distinctness of labels is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom] (g : T ⟶ S)
  (H : (E.baseChange g).FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)
  (a : Labels 4 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))
  (b : Labels 3 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))

include hc ha in
/-- The ample chart covers original tests with every auxiliary label and generator retained. -/
theorem exists_original_unrestricted_marked_ample_test :
    ∃ (U : Scheme) (q : U ⟶ T), Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      ∃ (P : 𝟙_ (Over U) ⟶ (H.baseChange q).carrier)
        (_ : (H.baseChange q).IsCartierGenerator P)
        (v : U ⟶ (unrestrictedAmpleOpen E n).toScheme)
        (d : FiniteSubgroup.CompatibleIso (H.baseChange q)
          ((unrestrictedAmpleLevel E n).val.2.baseChange v)),
        (∀ j, pullSection q (a j) ≫ d.curve.hom.group =
          pullSection v (unrestrictedAmpleLabel E n (j, 1, 1))) ∧
        (∀ j, pullSection q (b j) ≫ d.curve.hom.group =
          pullSection v (unrestrictedAmpleLabel E n (1, j, 1))) ∧
        P ≫ d.subgroup.hom = pullSection v (unrestrictedAmpleGenerator E n) := by
  obtain ⟨U, q, hf, hs, hl, P, hP, k, d, hA, hB, hG⟩ :=
    exists_original_unrestricted_test E n g H hc a b
  let v := unrestrictedAmpleLift E n (H.baseChange q) k d (ha.baseChange q)
  let e := unrestrictedAmpleLiftSubgroupIso E n (H.baseChange q) k d (ha.baseChange q)
  refine ⟨U, q, hf, hs, hl, P, hP, v, e, ?_, ?_, ?_⟩
  · intro j
    exact unrestrictedAmpleLiftSubgroupIso_label E n (H.baseChange q) k d
      (ha.baseChange q) (j, 1, 1) _ (hA j)
  · intro j
    exact unrestrictedAmpleLiftSubgroupIso_label E n (H.baseChange q) k d
      (ha.baseChange q) (1, j, 1) _ (hB j)
  · exact unrestrictedAmpleLiftSubgroupIso_generator E n (H.baseChange q) k d
      (ha.baseChange q) P hG

end FLT.Mazur.CyclicBoundaryParameter
