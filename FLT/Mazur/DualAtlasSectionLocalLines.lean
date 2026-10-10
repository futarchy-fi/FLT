/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionChartPoints
public import FLT.Mazur.AffineProjectivePointLineCover

/-!
# Actual normalized local lines of a dual atlas section

Each genuine finite free chart point of a global section admits an affine
cover by normalized section lines. Both the coefficient map and the equality
with the original atlas section are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasSectionChartPoints
open FCurve AffineFiniteFreeAtlas LocallyFreeDualProjectiveAtlas
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)
variable (s : X ⟶ space M hM) (hs : s ≫ projection M hM = 𝟙 X)

/-- The lifted point has exactly the original coefficient-spectrum projection. -/
lemma point_baseProjection (i : Index M) :
    point M hM s hs i ≫ ProjectiveSpace.baseProjection Γ(i.val.toScheme, ⊤)
      (coordinates M i) = i.val.toScheme.isoSpec.hom := by
  have h := point_projection M hM s hs i
  apply (cancel_mono i.val.toScheme.isoSpec.inv).mp
  simpa only [ProjectiveSpace.affineProjection, Category.assoc, Iso.hom_inv_id] using h

/-- Normalized actual line charts exist around every point of each original affine base chart. -/
lemma exists_local_line (i : Index M) (x : i.val.toScheme) :
    ∃ (U : i.val.toScheme.Opens) (hU : IsAffine U.toScheme), x ∈ U ∧
      let _ := hU
      ∃ (k : coordinates M i)
        (L : NormalizedSectionLine.Chart Γ(U.toScheme, ⊤) (coordinates M i) k),
        U.ι ≫ point M hM s hs i = ProjectiveSpace.affineSectionLinePoint U.ι.appTop.hom k L := by
  have hp : point M hM s hs i ≫
      ProjectiveSpace.baseProjection Γ(i.val.toScheme, ⊤) (coordinates M i) =
        i.val.toScheme.isoSpec.hom ≫ Spec.map
          (CommRingCat.ofHom (RingHom.id Γ(i.val.toScheme, ⊤))) := by
    change _ = i.val.toScheme.isoSpec.hom ≫ Spec.map (𝟙 _)
    rw [Spec.map_id, Category.comp_id]
    exact point_baseProjection M hM s hs i
  simpa only [RingHom.comp_id] using
    ProjectiveSpace.exists_local_sectionLine (.id _) (point M hM s hs i) hp x

/-- Every recovered local line classifies the original global atlas section. -/
lemma local_line_chartMap (i : Index M) (U : i.val.toScheme.Opens) [IsAffine U.toScheme]
    (k : coordinates M i)
    (L : NormalizedSectionLine.Chart Γ(U.toScheme, ⊤) (coordinates M i) k)
    (h : U.ι ≫ point M hM s hs i = ProjectiveSpace.affineSectionLinePoint U.ι.appTop.hom k L) :
    ProjectiveSpace.affineSectionLinePoint U.ι.appTop.hom k L ≫ chartMap M hM i =
      (U.ι ≫ i.val.ι) ≫ s := by
  rw [← h, Category.assoc, point_chartMap, Category.assoc]

end FLT.Mazur.DualAtlasSectionChartPoints
