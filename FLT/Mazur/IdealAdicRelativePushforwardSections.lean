/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeProjectionSections
public import FLT.Mazur.IdealAdicRelativePushforwardOpens

/-!
# Affine sections of the descended coefficient pushforward

The actual affine pushforward to the original scheme recovers the original
total coefficient module on every affine open, through its canonical projection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeChartCoefficientSheaf relativeDescendedCoefficientSheaf

/-- The actual affine pushforward of the descended coherent coefficient module. -/
def relativeDescendedCoefficientPushforward : X.Modules :=
  (pushforward (relativeSchemeToSource J f)).obj (relativeDescendedCoefficientSheaf J f)

/-- Pushforward sections on an original affine open are sections on its tensor image. -/
def relativePushforwardImageSectionsIso (U : X.affineOpens) :
    Γ(relativeDescendedCoefficientPushforward J f, U.1) ≅
      Γ(relativeDescendedCoefficientSheaf J f, relativeTensorImageOpen J f U) :=
  (relativeDescendedCoefficientSheaf J f).presheaf.mapIso
    (eqToIso (relativeSchemeToSource_preimage J f U).symm).op

/-- Canonical projection identifies affine pushforward sections with original coefficients. -/
def relativePushforwardCoefficientSectionsIso (U : X.affineOpens) :
    Γ(relativeDescendedCoefficientPushforward J f, U.1) ≅
      AddCommGrpCat.of (IdealAdicGradedSections.Sections (J.comap f) U.1) :=
  relativePushforwardImageSectionsIso J f U ≪≫
    relativeDescendedCoefficientImageSectionsIso J f U

/-- Reindexing the pushforward sections commutes with original affine restrictions. -/
lemma relativePushforwardImageSectionsIso_naturality {U V : X.affineOpens}
    (i : U.1 ⟶ V.1) :
    (relativeDescendedCoefficientPushforward J f).presheaf.map i.op ≫
        (relativePushforwardImageSectionsIso J f U).hom =
      (relativePushforwardImageSectionsIso J f V).hom ≫
        (relativeDescendedCoefficientSheaf J f).presheaf.map
          (homOfLE (relativeTensorImageOpen_mono J f i)).op := by
  change (relativeDescendedCoefficientSheaf J f).presheaf.map _ ≫
      (relativeDescendedCoefficientSheaf J f).presheaf.map _ =
    (relativeDescendedCoefficientSheaf J f).presheaf.map _ ≫
      (relativeDescendedCoefficientSheaf J f).presheaf.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

end FLT.Mazur.IdealAdicGradedPullback
