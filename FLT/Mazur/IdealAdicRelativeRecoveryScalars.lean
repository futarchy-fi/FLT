/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeGeometricScalars
public import FLT.Mazur.IdealAdicRelativeDescendedScalars
public import FLT.Mazur.ModuleSheafSectionScalars

/-!
# Geometric scalars under actual affine coefficient recovery

The additive affine recovery is linear for the original structure-sheaf
scalar action inherited from its geometric pushforward.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.ModuleSheafSectionScalars

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] relativeDescendedCoefficientSheaf relativeChartCoefficientSheaf

/-- Reindexing the actual pushforward retains its geometric scalar pullback. -/
lemma relativePushforwardImageSectionsIso_geometric_smul (U : X.affineOpens)
    (r : Γ(X, U.1)) (s : Γ(relativeDescendedCoefficientPushforward J f, U.1)) :
    (relativePushforwardImageSectionsIso J f U).hom (r • s) =
      (relativeSchemeToSource J f).appLE U.1 (relativeTensorImageOpen J f U)
        (relativeSchemeToSource_preimage J f U).ge r •
          (relativePushforwardImageSectionsIso J f U).hom s :=
  pushforward_reindex_smul (relativeSchemeToSource J f)
    (relativeDescendedCoefficientSheaf J f) U.1 (relativeTensorImageOpen J f U)
    (relativeSchemeToSource_preimage J f U) r s

/-- Reindexing ambient chart sections retains the actual chart scalar map. -/
lemma relativeAmbientCoefficientTopIso_geometric_smul (U : X.affineOpens)
    (r : Γ(relativeScheme J f, relativeTensorImageOpen J f U))
    (s : Γ(relativeAmbientCoefficient J f U, relativeTensorImageOpen J f U)) :
    (relativeAmbientCoefficientTopIso J f U).hom (r • s) =
      (relativeTensorChart J f U).appLE (relativeTensorImageOpen J f U) ⊤
        (Scheme.Hom.preimage_opensRange (relativeTensorChart J f U)).ge r •
          (relativeAmbientCoefficientTopIso J f U).hom s :=
  pushforward_reindex_smul (relativeTensorChart J f U)
    (relativeChartCoefficientSheaf J f U) (relativeTensorImageOpen J f U) ⊤
    (Scheme.Hom.preimage_opensRange (relativeTensorChart J f U)) r s

/-- The actual projection into chart global sections preserves original source scalars. -/
lemma relativePushforwardChartSections_geometric_smul (U : X.affineOpens)
    (r : Γ(X, U.1)) (s : Γ(relativeDescendedCoefficientPushforward J f, U.1)) :
    (relativeAmbientCoefficientTopIso J f U).hom
        ((relativeDescendedCoefficientProjection J f U).app (relativeTensorImageOpen J f U)
          ((relativePushforwardImageSectionsIso J f U).hom (r • s))) =
      (Scheme.ΓSpecIso (.of (RelativeAlgebra J f U))).inv (relativeChartScalar J f U r) •
        (relativeAmbientCoefficientTopIso J f U).hom
          ((relativeDescendedCoefficientProjection J f U).app (relativeTensorImageOpen J f U)
            ((relativePushforwardImageSectionsIso J f U).hom s)) := by
  rw [relativePushforwardImageSectionsIso_geometric_smul,
    (relativeDescendedCoefficientProjection J f U).app_smul,
    relativeAmbientCoefficientTopIso_geometric_smul]
  congr 1
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE,
    relativeTensorChart_source_scalar, ConcreteCategory.comp_apply]
  rfl

/-- Affine recovery is linear for the geometric source structure-sheaf action. -/
lemma relativePushforwardCoefficientSectionsIso_geometric_smul (U : X.affineOpens)
    (r : Γ(X, U.1)) (s : Γ(relativeDescendedCoefficientPushforward J f, U.1)) :
    (relativePushforwardCoefficientSectionsIso J f U).hom (r • s) =
      r • (show IdealAdicGradedSections.Sections (J.comap f) U.1 from
        (relativePushforwardCoefficientSectionsIso J f U).hom s) := by
  let := closedBaseAlgebra J f U.1
  have h := relativePushforwardChartSections_geometric_smul J f U r s
  have he (t : Γ(relativeDescendedCoefficientPushforward J f, U.1)) :
      (relativeChartCoefficientSectionsIso J f U).hom
          ((relativePushforwardCoefficientSectionsIso J f U).hom t) =
        (relativeAmbientCoefficientTopIso J f U).hom
          ((relativeDescendedCoefficientProjection J f U).app (relativeTensorImageOpen J f U)
            ((relativePushforwardImageSectionsIso J f U).hom t)) := by
    unfold relativePushforwardCoefficientSectionsIso relativeDescendedCoefficientImageSectionsIso
    simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv,
      ConcreteCategory.comp_apply]
    erw [(relativeChartCoefficientSectionsIso J f U).inv_hom_id_apply]
    simp only [relativeDescendedCoefficientProjectionIso, asIso_hom]
  rw [← he, ← he] at h
  apply (ConcreteCategory.bijective_of_isIso
    (relativeChartCoefficientSectionsIso J f U).hom).injective
  rw [← relativeChartScalar_smul J f U r]
  exact h.trans ((relativeChartCoefficientSectionsIso J f U).hom.hom.map_smul
    (relativeChartScalar J f U r) _).symm

attribute [local irreducible] relativeDescendedCoefficientPushforward
attribute [local irreducible] relativePushforwardCoefficientSectionsIso

/-- Canonical affine recovery with the actual geometric structure-module actions. -/
def relativePushforwardCoefficientLinearEquiv (U : X.affineOpens) :
    Γ(relativeDescendedCoefficientPushforward J f, U.1) ≃ₗ[Γ(X, U.1)]
      IdealAdicGradedSections.Sections (J.comap f) U.1 where
  toFun := (relativePushforwardCoefficientSectionsIso J f U).hom
  invFun := (relativePushforwardCoefficientSectionsIso J f U).inv
  left_inv := (relativePushforwardCoefficientSectionsIso J f U).hom_inv_id_apply
  right_inv := (relativePushforwardCoefficientSectionsIso J f U).inv_hom_id_apply
  map_add' := (relativePushforwardCoefficientSectionsIso J f U).hom.hom.map_add
  map_smul' := relativePushforwardCoefficientSectionsIso_geometric_smul J f U

/-- Relative multiplication by a source chart scalar is the actual geometric action. -/
lemma relativeDescendedRelativeSmul_chartScalar (U : X.affineOpens)
    (r : Γ(X, U.1)) (s : Γ(relativeDescendedCoefficientPushforward J f, U.1)) :
    relativeDescendedRelativeSmul J f U.1
        ((relativeChartIso J f U).hom (relativeChartScalar J f U r)) s = r • s := by
  apply (relativePushforwardCoefficientLinearEquiv J f U).injective
  change (relativePushforwardCoefficientSectionsIso J f U).hom _ =
    (relativePushforwardCoefficientSectionsIso J f U).hom _
  rw [relativePushforwardCoefficientSectionsIso_relativeAction, relativeChartScalar_smul,
    relativePushforwardCoefficientSectionsIso_geometric_smul]

end FLT.Mazur.IdealAdicGradedPullback
