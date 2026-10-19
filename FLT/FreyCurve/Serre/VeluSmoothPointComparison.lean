/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothRestriction
public import FLT.Mazur.WeierstrassLeftSmoothSectionTranslation
public import FLT.Mazur.WeierstrassSmoothProjectiveGroup

/-!
# Original affine points in the whole-cubic action

The existing smooth point comparison identifies the whole-cubic action with
addition of the original affine points over every coefficient field extension.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L] (E : WeierstrassCurve K)

/-- The original affine point as a point of the actual relative smooth locus. -/
def affineSmoothPoint (P : (E.map (algebraMap K L)).toAffine.Point) :
    Spec (.of L) ⟶ (integralSmoothOpen E).toScheme :=
  projectiveToSmooth E (Projective.Point.fromAffine P)

/-- Its coefficient morphism is the original field extension. -/
@[reassoc] theorem affineSmoothPoint_structure
    (P : (E.map (algebraMap K L)).toAffine.Point) :
    affineSmoothPoint E P ≫ integralSmoothStructure E =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
  projectiveToSmooth_structure E _

/-- The enlarged action on two smooth points is the original smooth multiplication. -/
theorem leftSmoothPointAddition_smooth {X : Scheme}
    (a b : X ⟶ (integralSmoothOpen E).toScheme)
    (h : a ≫ integralSmoothStructure E = b ≫ integralSmoothStructure E) :
    leftSmoothPointAddition E a (b ≫ (integralSmoothOpen E).ι) h =
      smoothPairPointAddition E a b h ≫ (integralSmoothOpen E).ι := by
  have hp : pullback.lift a (b ≫ (integralSmoothOpen E).ι) h =
      pullback.lift a b h ≫ smoothFactorsToLeftSmooth E := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, smoothFactorsToLeftSmooth_fst,
        smoothFactorsToLeftSmooth_snd, pullback.lift_fst, pullback.lift_snd_assoc,
        pullback.lift_snd]
  rw [leftSmoothPointAddition, hp, Category.assoc, smoothFactorsToLeftSmooth_addition]
  rfl

/-- Smooth scheme addition retains the actual affine point sum. -/
theorem affineSmoothPoint_add [DecidableEq L]
    (P Q : (E.map (algebraMap K L)).toAffine.Point) :
    affineSmoothPoint E (P + Q) =
      smoothPairPointAddition E (affineSmoothPoint E P) (affineSmoothPoint E Q)
        (by rw [affineSmoothPoint_structure, affineSmoothPoint_structure]) := by
  have he := congrArg Over.Hom.left (projectiveToSmoothOver_add E
    (Projective.Point.fromAffine P) (Projective.Point.fromAffine Q))
  have ha : Projective.Point.fromAffine (P + Q) =
      Projective.Point.fromAffine P + Projective.Point.fromAffine Q :=
    (Projective.Point.toAffineAddEquiv
      (E.map (algebraMap K L)).toProjective).symm.map_add P Q
  simp only [Over.comp_left, Over.lift_left,
    projectiveToSmoothOver, integralSmoothOverAddition, Over.homMk_left] at he
  simp only [affineSmoothPoint, ha, smoothPairPointAddition]
  exact he

/-- The action on original affine points gives their original sum in the whole cubic. -/
theorem affineSmoothPoint_action [DecidableEq L]
    (P Q : (E.map (algebraMap K L)).toAffine.Point) :
    leftSmoothPointAddition E (affineSmoothPoint E P)
        (affineSmoothPoint E Q ≫ (integralSmoothOpen E).ι)
        (by rw [Category.assoc, affineSmoothPoint_structure,
          ← affineSmoothPoint_structure E Q]) =
      affineSmoothPoint E (P + Q) ≫ (integralSmoothOpen E).ι := by
  rw [leftSmoothPointAddition_smooth, ← affineSmoothPoint_add]

end WeierstrassCurve.Velu
