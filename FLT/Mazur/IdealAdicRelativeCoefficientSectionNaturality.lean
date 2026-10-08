/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeRecoverySectionRefinement

/-!
# Naturality of the actual coefficient pushforward sections

The recovered coefficients restrict by the original `restrictRingHom`.
This proves the full affine-section naturality square, beyond reindexing
of the chart image opens.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.IdealAdicGradedSections

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback
attribute [local irreducible] relativeDescendedCoefficientSheaf relativeCoefficientSheafMap

/-- The coefficient transition sends an actual pullback unit to the original restriction. -/
lemma relativeCoefficientSheafMap_unit_sections {U V : X.affineOpens} (i : U.1 ⟶ V.1)
    (s : relativeChartCoefficient J f V) :
    (relativeCoefficientSheafMap J f i).app ⊤
        (((pullbackPushforwardAdjunction (relativeTensorTransition J f i)).unit.app
          (relativeChartCoefficientSheaf J f V)).app ⊤
            ((relativeChartCoefficientSectionsIso J f V).hom s)) =
      (relativeChartCoefficientSectionsIso J f U).hom (restrictRingHom (J.comap f) U.1 i s) :=
  relativeCoefficientSheafMap_unit J f i s

attribute [local irreducible] relativeChartCoefficientSheaf

/-- The coefficient recovered on an image has the original tilde section as its recovery. -/
lemma relativeDescendedCoefficientImageSectionsIso_apply (U : X.affineOpens)
    (s : Γ(relativeDescendedCoefficientSheaf J f, relativeTensorImageOpen J f U)) :
    (relativeChartCoefficientSectionsIso J f U).hom
        ((relativeDescendedCoefficientImageSectionsIso J f U).hom s) =
      (relativeDescendedAffineRecoveryIso J f (𝟙 U.1)).hom.app ⊤
        ((relativeDescendedImagePullbackSectionsIso J f U).hom s) := by
  rw [relativeDescendedCoefficientImageSectionsIso_recovery]
  exact (relativeChartCoefficientSectionsIso J f U).inv_hom_id_apply _

attribute [local irreducible] relativeDescendedCoefficientImageSectionsIso
attribute [local irreducible] relativeDescendedImagePullbackSectionsIso
attribute [local irreducible] relativeDescendedAffineRecoveryIso relativeChartCoefficientSectionsIso

/-- Restriction of actual image sections induces the original coefficient restriction. -/
lemma relativeDescendedCoefficientImageSectionsIso_naturality {U V : X.affineOpens}
    (i : U.1 ⟶ V.1) :
    (relativeDescendedCoefficientSheaf J f).presheaf.map
        (homOfLE (relativeTensorImageOpen_mono J f i)).op ≫
          (relativeDescendedCoefficientImageSectionsIso J f U).hom =
      (relativeDescendedCoefficientImageSectionsIso J f V).hom ≫
        AddCommGrpCat.ofHom (restrictRingHom (J.comap f) U.1 i).toAddMonoidHom := by
  apply ConcreteCategory.hom_ext
  intro s
  simp only [ConcreteCategory.comp_apply]
  apply (ConcreteCategory.bijective_of_isIso
    (relativeChartCoefficientSectionsIso J f U).hom).injective
  rw [relativeDescendedCoefficientImageSectionsIso_apply]
  have hr := congrArg (fun a ↦ a s)
    (relativeDescendedAffineRecoveryIso_sections_refine J f i)
  simp only [ConcreteCategory.comp_apply] at hr
  rw [hr, ← relativeDescendedCoefficientImageSectionsIso_apply]
  exact relativeCoefficientSheafMap_unit_sections J f i
    ((relativeDescendedCoefficientImageSectionsIso J f V).hom s)

/-- The actual affine pushforward comparison is natural for original coefficient restrictions. -/
lemma relativePushforwardCoefficientSectionsIso_naturality {U V : X.affineOpens}
    (i : U.1 ⟶ V.1) :
    (relativeDescendedCoefficientPushforward J f).presheaf.map i.op ≫
        (relativePushforwardCoefficientSectionsIso J f U).hom =
      (relativePushforwardCoefficientSectionsIso J f V).hom ≫
        AddCommGrpCat.ofHom (restrictRingHom (J.comap f) U.1 i).toAddMonoidHom := by
  unfold relativePushforwardCoefficientSectionsIso
  simp only [Iso.trans_hom]
  rw [← Category.assoc, relativePushforwardImageSectionsIso_naturality, Category.assoc,
    relativeDescendedCoefficientImageSectionsIso_naturality, Category.assoc]

end FLT.Mazur.IdealAdicGradedPullback
