/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientProductMorphism
public import FLT.Mazur.WeierstrassIntegralBaseChange
public import FLT.Mazur.WeierstrassIntegralGroupOperations

/-!
# The actual cubic base-change comparison in the monoidal slice

The original Cartesian coefficient square supplies an isomorphism over the
new base. Its tensor comparison retains both actual proper coefficient maps.
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

/-- The original coefficient base-change comparison, now over the new base. -/
def integralCurveCoefficientOverIso : integralCurveOver V ≅ (F).obj (integralCurveOver W) :=
  Over.isoMk (integralCurveCoefficientBaseChangeIso W)
    (integralCurveCoefficientBaseChangeIso_snd W)

/-- The comparison retains the original global coefficient morphism. -/
@[reassoc] theorem integralCurveCoefficientOverIso_fst :
    (integralCurveCoefficientOverIso (S := S) W).hom.left ≫ pullback.fst _ _ =
      integralCoefficientMorphism W := integralCurveCoefficientBaseChangeIso_fst W

/-- The tensor comparison is the actual coefficient map on both proper inputs. -/
@[reassoc] theorem integralCurveCoefficientOverIso_product :
    (((integralCurveCoefficientOverIso (S := S) W).hom ⊗ₘ
      (integralCurveCoefficientOverIso (S := S) W).hom) ≫
        Functor.LaxMonoidal.μ F _ _).left ≫
          pullback.fst (integralCurveOver W ⊗ integralCurveOver W).hom
            (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      integralCoefficientProduct W := by
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    rw [Over.μ_pullback_left_fst_fst]
    erw [Over.tensorHom_left_fst_assoc]
    rw [integralCurveCoefficientOverIso_fst]
    exact (integralCoefficientProduct_fst (S := S) W).symm
  · simp only [Over.comp_left, Category.assoc]
    rw [Over.μ_pullback_left_fst_snd]
    erw [Over.tensorHom_left_snd_assoc]
    rw [integralCurveCoefficientOverIso_fst]
    exact (integralCoefficientProduct_snd (S := S) W).symm

end FLT.Mazur.WeierstrassIntegralChart
