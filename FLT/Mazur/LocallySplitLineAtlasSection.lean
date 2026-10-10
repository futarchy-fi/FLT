/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitLineDualChartCompatibility

/-!
# The global dual projective atlas section of an actual line subbundle

Local rank one and local splitting construct reverse points compatible with
the actual finite free atlas. Descent along the locally directed affine base
cover gives an actual global section of the dual projective atlas projection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallySplitLineAtlasSection
open FCurve SplitLineAffineNeighborhood LocallySplitLineAmbientChart
variable {X : Scheme.{u}} {L M : X.Modules} (s : L ⟶ M)
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s) (hM : LocallyFiniteFree M)

/-- The constructed atlas-valued points respect actual inclusions of affine free opens. -/
lemma atlasPoint_refinement {i j : AffineFiniteFreeAtlas.Index M} (h : i ≤ j) :
    X.homOfLE h ≫ atlasPoint s hL hs hM j = atlasPoint s hL hs hM i := by
  rw [atlasPoint, ← Category.assoc, ← point_dualChartInclusion s hL hs h
      (AffineFiniteFreeAtlas.chart M i) (AffineFiniteFreeAtlas.chart M j),
    Category.assoc, atlasPoint]
  apply congrArg (point s hL hs i.val (AffineFiniteFreeAtlas.chart M i) ≫ ·)
  exact colimit.w (LocallyFreeDualProjectiveAtlas.gluingData M hM).functor (homOfLE h)

/-- Actual reverse points form a cocone on the original affine base cover. -/
def pointCocone : Cocone (AffineFiniteFreeAtlas.cover M hM).functorOfLocallyDirected where
  pt := LocallyFreeDualProjectiveAtlas.space M hM
  ι :=
    { app i := atlasPoint s hL hs hM i
      naturality := by
        intro i j f
        change X.homOfLE f.le ≫ atlasPoint s hL hs hM j =
          atlasPoint s hL hs hM i ≫ 𝟙 _
        rw [Category.comp_id]
        exact atlasPoint_refinement s hL hs hM f.le }

/-- The global reverse morphism to the actual dual projective atlas. -/
def morphism : X ⟶ LocallyFreeDualProjectiveAtlas.space M hM :=
  (AffineFiniteFreeAtlas.baseIsColimit M hM).desc (pointCocone s hL hs hM)

/-- The descended morphism recovers every original ambient chart point. -/
@[reassoc]
lemma ι_morphism (i : AffineFiniteFreeAtlas.Index M) :
    i.val.ι ≫ morphism s hL hs hM = atlasPoint s hL hs hM i :=
  (AffineFiniteFreeAtlas.baseIsColimit M hM).fac (pointCocone s hL hs hM) i

/-- The global reverse morphism is an actual section of the projective atlas projection. -/
lemma morphism_projection :
    morphism s hL hs hM ≫ LocallyFreeDualProjectiveAtlas.projection M hM = 𝟙 X := by
  apply (AffineFiniteFreeAtlas.cover M hM).hom_ext
  intro i
  change i.val.ι ≫ (morphism s hL hs hM ≫ _) = i.val.ι ≫ 𝟙 X
  rw [ι_morphism_assoc, atlasPoint_projection, Category.comp_id]

/-- The actual affine reverse points uniquely determine the global atlas section. -/
lemma morphism_unique (p : X ⟶ LocallyFreeDualProjectiveAtlas.space M hM)
    (hp : ∀ i : AffineFiniteFreeAtlas.Index M, i.val.ι ≫ p = atlasPoint s hL hs hM i) :
    p = morphism s hL hs hM := by
  apply (AffineFiniteFreeAtlas.cover M hM).hom_ext
  intro i
  exact (hp i).trans (ι_morphism s hL hs hM i).symm

end FLT.Mazur.LocallySplitLineAtlasSection
