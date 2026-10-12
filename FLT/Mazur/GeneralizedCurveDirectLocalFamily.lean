/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveDirectLocalCubic
public import FLT.Mazur.GeneralizedCurveIdentityBaseChange
public import FLT.Mazur.GeneralizedCurvePointedCubicFamily

/-!
# Local full DR presentations of the original smooth base locus

The original curve, group and action are locally isomorphic to the established
cubic family. The full comparison retains the originally constructed coefficients
and complete pointed curve map, on the original single base change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{0}} (E : GeneralizedEllipticCurve S) [IsLocallyNoetherian S]

/-- Every original smooth base point has a full DR cubic chart inside any given neighborhood. -/
theorem exists_original_local_cubicFamily {V : S.Opens} {x : S}
    (hx : x ∈ smoothBaseOpen E) (hxV : x ∈ V) :
    ∃ (T : Scheme) (_ : IsAffine T) (g : T ⟶ S),
      IsOpenImmersion g ∧ x ∈ Set.range g ∧ Set.range g ⊆ V ∧
        ∃ (W : WeierstrassCurve Γ(T, ⊤)) (_ : W.IsElliptic)
          (e : (E.baseChange g).curve.left ≅ integralCurve W),
          e.hom ≫ integralCurveStructure W = (E.baseChange g).curve.hom ≫ T.toSpecΓ ∧
          (pullSection g E.identitySection).left ≫ e.hom =
            T.toSpecΓ ≫ integralCurveZero W ∧
          ∃ d : E.baseChange g ≅ pointedCubicFamily W,
            d.hom.curve.left ≫ pullback.fst (integralCurveStructure W) T.toSpecΓ = e.hom := by
  obtain ⟨T, hT, g, hg, hxg, hV, W, hW, e, he, hs⟩ :=
    exists_original_local_pointedCubic E E.identitySection hx hxV
  let _ := hT
  let _ := hg
  let _ := hW
  let _ := isLocallyNoetherian_of_isOpenImmersion g
  have hz : (E.baseChange g).identitySection.left ≫ e.hom =
      T.toSpecΓ ≫ integralCurveZero W := by
    rw [← pullSection_identity]
    exact hs
  exact ⟨T, hT, g, hg, hxg, hV, W, hW, e, he, hs,
    pointedCubicFamilyIso W (E.baseChange g) e he hz,
    pointedCubicFamilyIso_curve_fst W (E.baseChange g) e he hz⟩

end FLT.Mazur.GeneralizedEllipticCurve
