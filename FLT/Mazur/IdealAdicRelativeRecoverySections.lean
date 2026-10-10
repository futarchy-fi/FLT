/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeRecoveryIdentity
public import FLT.Mazur.IdealAdicRelativePushforwardSections
public import FLT.Mazur.ModuleSheafOpenImmersionTopSections

/-!
# Section normalization of descended coefficient recovery

The established coefficient-section isomorphism is exactly the section map
of the self-chart recovery. The comparison uses the actual immersion unit
and the original tilde section isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafOpenImmersionSections

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeDescendedCoefficientSheaf

/-- Image sections enter the actual pullback through its canonical section isomorphism. -/
def relativeDescendedImagePullbackSectionsIso (U : X.affineOpens) :
    Γ(relativeDescendedCoefficientSheaf J f, relativeTensorImageOpen J f U) ≅
      Γ((pullback (relativeTensorChart J f U)).obj (relativeDescendedCoefficientSheaf J f), ⊤) :=
  topSectionsIso (relativeTensorChart J f U) (relativeDescendedCoefficientSheaf J f)

/-- Applying recovery to a chart section is the original descended projection. -/
lemma relativeDescendedImagePullbackSectionsIso_recovery (U : X.affineOpens) :
    (relativeDescendedImagePullbackSectionsIso J f U).hom ≫
        (relativeDescendedAffineRecoveryIso J f (𝟙 U.1)).hom.app ⊤ =
      (relativeDescendedCoefficientProjection J f U).app (relativeTensorImageOpen J f U) ≫
        (relativeAmbientCoefficientTopIso J f U).hom := by
  rw [relativeDescendedAffineRecoveryIso_self, Hom.comp_app, ← Category.assoc]
  unfold relativeDescendedImagePullbackSectionsIso
  rw [← topSectionsIso_naturality, Category.assoc]
  exact congrArg ((relativeDescendedCoefficientProjection J f U).app
    (relativeTensorImageOpen J f U) ≫ ·)
    (topSectionsIso_counit (relativeTensorChart J f U) (relativeChartCoefficientSheaf J f U))

/-- The image coefficient comparison is the section map of actual affine recovery. -/
lemma relativeDescendedCoefficientImageSectionsIso_recovery (U : X.affineOpens) :
    (relativeDescendedCoefficientImageSectionsIso J f U).hom =
      (relativeDescendedImagePullbackSectionsIso J f U).hom ≫
        (relativeDescendedAffineRecoveryIso J f (𝟙 U.1)).hom.app ⊤ ≫
          (forget₂ (ModuleCat (RelativeAlgebra J f U)) AddCommGrpCat).map
            (relativeChartCoefficientSectionsIso J f U).inv := by
  rw [← Category.assoc, relativeDescendedImagePullbackSectionsIso_recovery, Category.assoc]
  rfl

/-- The actual pushforward section comparison is computed by self-chart recovery. -/
lemma relativePushforwardCoefficientSectionsIso_recovery (U : X.affineOpens) :
    (relativePushforwardCoefficientSectionsIso J f U).hom =
      (relativePushforwardImageSectionsIso J f U).hom ≫
        (relativeDescendedImagePullbackSectionsIso J f U).hom ≫
          (relativeDescendedAffineRecoveryIso J f (𝟙 U.1)).hom.app ⊤ ≫
            (forget₂ (ModuleCat (RelativeAlgebra J f U)) AddCommGrpCat).map
              (relativeChartCoefficientSectionsIso J f U).inv := by
  exact congrArg ((relativePushforwardImageSectionsIso J f U).hom ≫ ·)
    (relativeDescendedCoefficientImageSectionsIso_recovery J f U)

end FLT.Mazur.IdealAdicGradedPullback
