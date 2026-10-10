/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientMonoidalComparison
public import FLT.Mazur.WeierstrassCoefficientZero
public import FLT.Mazur.WeierstrassCoefficientAddition
public import FLT.Mazur.WeierstrassIntegralGroup
public import FLT.Mazur.GroupSectionBaseChange

/-!
# Actual coefficient base change is an isomorphism of group schemes

The original Cartesian cubic comparison preserves the constructed zero and
addition. Its group isomorphism therefore uses the actual monoidal pullback.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

local notation "V" => W.map (algebraMap R S)

local notation "F" => Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The original coefficient comparison preserves the actual monoidal zero. -/
theorem integralCurveCoefficientOverIso_zero :
    integralCurveOverZero V ≫ (integralCurveCoefficientOverIso (S := S) W).hom =
      Functor.LaxMonoidal.ε F ≫ (F).map (integralCurveOverZero W) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change integralCurveZero V ≫
      (integralCurveCoefficientOverIso (S := S) W).hom.left ≫ pullback.fst _ _ = _
    rw [integralCurveCoefficientOverIso_fst]
    exact (integralCoefficientMorphism_zero W).trans
      (GroupSectionBaseChange.section_fst _ (integralCurveOverZero W)).symm
  · exact (integralCurveOverZero V ≫ (integralCurveCoefficientOverIso W).hom).w.trans
      (Functor.LaxMonoidal.ε F ≫ (F).map (integralCurveOverZero W)).w.symm

/-- The original coefficient comparison preserves actual monoidal addition. -/
theorem integralCurveCoefficientOverIso_addition
    (hW : IsUnit W.Δ) (hV : IsUnit (V).Δ) :
    integralCurveOverAddition V hV ≫ (integralCurveCoefficientOverIso (S := S) W).hom =
      ((integralCurveCoefficientOverIso W).hom ⊗ₘ
        (integralCurveCoefficientOverIso W).hom) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ (F).map (integralCurveOverAddition W hW) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [integralCurveCoefficientOverIso_fst]
    rw [← Category.assoc _ (Functor.LaxMonoidal.μ F _ _).left,
      ← Over.comp_left, integralCurveCoefficientOverIso_product_assoc]
    exact integralCoefficientMorphism_addition W hW hV
  · exact (integralCurveOverAddition V hV ≫
      (integralCurveCoefficientOverIso W).hom).w.trans
        (((integralCurveCoefficientOverIso W).hom ⊗ₘ
          (integralCurveCoefficientOverIso W).hom) ≫
            Functor.LaxMonoidal.μ F _ _ ≫ (F).map (integralCurveOverAddition W hW)).w.symm

/-- The actual cubic base-change isomorphism respects the original commutative group objects. -/
def integralCurveCoefficientGroupIso (hW : IsUnit W.Δ) (hV : IsUnit (V).Δ) :
    integralCurveGroup V hV ≅ (F).mapCommGrp.obj (integralCurveGroup W hW) :=
  CommGrp.mkIso (integralCurveCoefficientOverIso W)
    (integralCurveCoefficientOverIso_zero W)
    (integralCurveCoefficientOverIso_addition W hW hV)

/-- Forgetting group structure gives exactly the original Cartesian comparison. -/
theorem integralCurveCoefficientGroupIso_hom (hW : IsUnit W.Δ) (hV : IsUnit (V).Δ) :
    (integralCurveCoefficientGroupIso (S := S) W hW hV).hom.hom.hom.hom.left =
      (integralCurveCoefficientBaseChangeIso W).hom := rfl

/-- The inverse group isomorphism retains the exact original inverse scheme map. -/
theorem integralCurveCoefficientGroupIso_inv (hW : IsUnit W.Δ) (hV : IsUnit (V).Δ) :
    (integralCurveCoefficientGroupIso (S := S) W hW hV).inv.hom.hom.hom.left =
      (integralCurveCoefficientBaseChangeIso W).inv := rfl

end FLT.Mazur.WeierstrassIntegralChart
