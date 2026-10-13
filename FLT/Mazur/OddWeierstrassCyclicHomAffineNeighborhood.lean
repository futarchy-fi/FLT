/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicOriginalHomDivisorCoverage
public import FLT.Mazur.OddWeierstrassCyclicHomRetainedPullback

/-!
# Affine refinement of original odd cyclic families

Every original smooth cyclic family has affine fppf neighborhoods retaining
its full curve, finite subgroup, Cartier generator, and orbit ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  (hc : H.IsCyclic) (h₃ : IsUnit (3 : Γ(S, ⊤)))

include hc h₃ in
/-- Affine original neighborhoods keep the actual Cartier subgroup and every ideal factor. -/
theorem exists_affine_original_hom_neighborhood {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (R : CommRingCat) (g : Spec R ⟶ S),
      Flat g ∧ LocallyOfFinitePresentation g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (p : Spec R ⟶ (cyclicHomAuxiliaryScheme n).left)
          (J : (cyclicHomSourceCurve n p).FiniteSubgroup n),
          J.ideal = cyclicHomSourceIdeal n p ∧
            (∃ P, J.IsCartierGenerator P) ∧ Nonempty (CompatibleIso J (H.baseChange g)) := by
  obtain ⟨U, g, hg, hl, hxg, hV, p, J, hJ, ⟨P, hP⟩, ⟨a⟩⟩ :=
    exists_original_hom_divisor_neighborhood H hc h₃ hx
  obtain ⟨u, hu⟩ := hxg
  obtain ⟨i, v, hv⟩ := U.affineOpenCover.openCover.exists_eq u
  let k := U.affineOpenCover.f i
  let _ := hg
  let _ := hl
  refine ⟨U.affineOpenCover.X i, k ≫ g, inferInstance, inferInstance, ?_, ?_,
    k ≫ p, cyclicHomRetainedPullback p k J, cyclicHomRetainedPullback_ideal p k J hJ,
    ⟨J.pullGenerator k P, cyclicHomRetainedPullback_generator p k J hP⟩,
    ⟨(cyclicHomRetainedPullbackIso p k J).trans
      ((a.baseChange k).trans (compatibleBaseChangeComp H g k).symm)⟩⟩
  · exact ⟨v, (congrArg (fun z : U ↦ g z) hv).trans hu⟩
  · rintro _ ⟨v, rfl⟩
    exact hV ⟨k v, rfl⟩

end FLT.Mazur.OddWeierstrassParameter
