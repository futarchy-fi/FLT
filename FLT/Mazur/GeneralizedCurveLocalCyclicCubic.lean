/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicCyclicMarking
public import FLT.Mazur.GeneralizedCurveCyclicMarkingBaseChange
public import FLT.Mazur.GeneralizedCurveDirectLocalFamily

/-!
# Original cyclic subgroups in local full cubic charts

Start with an actual faithful presentation of the original subgroup. Every
smooth base point has an affine cubic neighborhood retaining the full cyclic
homomorphism, its original subgroup comparison, and each projected section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart UniversallyDistinctSections GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  {n : ℕ} [NeZero n] (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))
  (H : E.FiniteSubgroup n) (a : FiniteSubgroup.CompatibleIso (E.relativeCyclicSubgroup φ hφ) H)

include hφ a in
/-- Local cubic charts retain the original subgroup and every original cyclic section. -/
theorem exists_original_local_cyclicCubic {V : S.Opens} {x : S}
    (hx : x ∈ smoothBaseOpen E) (hxV : x ∈ V) :
    ∃ (T : Scheme) (_ : IsAffine T) (g : T ⟶ S),
      IsOpenImmersion g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (W : WeierstrassCurve Γ(T, ⊤)) (_ : W.IsElliptic)
          (e : (E.baseChange g).curve.left ≅ integralCurve W),
          e.hom ≫ integralCurveStructure W = (E.baseChange g).curve.hom ≫ T.toSpecΓ ∧
          (E.baseChange g).identitySection.left ≫ e.hom = T.toSpecΓ ≫ integralCurveZero W ∧
          ∃ (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over T) ⟶ (pointedCubicFamily W).group))
            (hψ : UniversallyDistinct (fun i : ZMod n ↦ ψ (.ofAdd i))),
            Nonempty (FiniteSubgroup.CompatibleIso
              ((pointedCubicFamily W).relativeCyclicSubgroup ψ hψ) (H.baseChange g)) ∧
            ∀ i, (ψ i).left ≫ pullback.fst (integralCurveStructure W) T.toSpecΓ =
              (pullCyclicMarking g φ i).left ≫ (E.baseChange g).inclusion.left ≫ e.hom := by
  obtain ⟨T, hT, g, hg, hxg, hV, W, hW, e, he, hs, _⟩ :=
    exists_original_local_cubicFamily E hx hxV
  let _ := hT
  let _ := hg
  let _ := hW
  let _ := isLocallyNoetherian_of_isOpenImmersion g
  have hz : (E.baseChange g).identitySection.left ≫ e.hom =
      T.toSpecΓ ≫ integralCurveZero W := by
    rw [← pullSection_identity]
    exact hs
  let ψ := pullCyclicMarking g φ
  have hψ := pullCyclicMarking_distinct g φ hφ
  exact ⟨T, hT, g, hg, hxg, hV, W, hW, e, he, hz,
    pointedCubicMarking (E.baseChange g) W e he hz ψ,
    pointedCubicMarking_distinct (E.baseChange g) W e he hz ψ hψ,
    ⟨pointedCubicMarkingOriginalIso (E.baseChange g) W e he hz ψ hψ (H.baseChange g)
      (pullCyclicMarkingOriginalIso g φ hφ H a)⟩,
    pointedCubicMarking_fst (E.baseChange g) W e he hz ψ⟩

end FLT.Mazur.GeneralizedEllipticCurve
