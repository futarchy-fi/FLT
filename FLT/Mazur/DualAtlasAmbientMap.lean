/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasAmbientCharts
public import FLT.Mazur.DualAtlasSectionTransport

/-!
# The global atlas morphism of an ambient sheaf isomorphism

The map descends from the original projective chart isomorphisms. It preserves
the base projection and every independently constructed reverse section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasAmbient
open FCurve AffineFiniteFreeAtlas LocallySplitLineAmbientChart
variable {X : Scheme.{u}} {M N : X.Modules} (a : M ≅ N)
variable (hM : LocallyFiniteFree M) (hN : LocallyFiniteFree N)

/-- Original transported chart maps form a cocone on the actual source atlas. -/
def cocone : Cocone (LocallyFreeDualProjectiveAtlas.gluingData M hM).functor where
  pt := LocallyFreeDualProjectiveAtlas.space N hN
  ι :=
    { app i := toAtlas a hN i
      naturality := by
        intro i j f
        change FiniteFreeChartTransitions.dualChartInclusion M f.le
          (chart M i) (chart M j) ≫ toAtlas a hN j = toAtlas a hN i ≫ 𝟙 _
        rw [Category.comp_id]
        exact toAtlas_refinement a hN f.le }

/-- The global scheme morphism descended from the original ambient chart maps. -/
def map : LocallyFreeDualProjectiveAtlas.space M hM ⟶
    LocallyFreeDualProjectiveAtlas.space N hN :=
  colimit.desc _ (cocone a hM hN)

/-- The global ambient map retains every original projective chart map. -/
@[reassoc]
lemma chart_map (i : Index M) :
    LocallyFreeDualProjectiveAtlas.chartMap M hM i ≫ map a hM hN = toAtlas a hN i :=
  colimit.ι_desc (cocone a hM hN) i

/-- Ambient transport is a morphism over the unchanged original base scheme. -/
@[reassoc]
lemma map_projection :
    map a hM hN ≫ LocallyFreeDualProjectiveAtlas.projection N hN =
      LocallyFreeDualProjectiveAtlas.projection M hM := by
  apply (LocallyFreeDualProjectiveAtlas.cover M hM).hom_ext
  intro i
  change LocallyFreeDualProjectiveAtlas.chartMap M hM i ≫ _ =
    LocallyFreeDualProjectiveAtlas.chartMap M hM i ≫ _
  rw [chart_map_assoc, toAtlas_projection, LocallyFreeDualProjectiveAtlas.chart_projection]

variable {L : X.Modules} (s : L ⟶ M) (hL : LocallyFreeRankOne L)
variable (hs : SplitLineAffineNeighborhood.LocallySplit s)

/-- The actual local reverse points commute with the ambient coordinate isomorphism. -/
lemma point_chartIso (i : Index M) :
    point s hL hs i.val (chart M i) ≫ (chartIso a i).hom =
      point (s ≫ a.hom) hL (hs.postcompose s a) i.val (chart N (index a i)) := by
  have hp := SplitLineAffinePresentation.morphism_ambientIso
    (inclusion s i.val (chart M i)) (hL.restrict i.val.ι)
    (inclusion_locallySplit s hs i.val (chart M i)) (change a i)
  apply hp.trans
  unfold point
  congr 1
  simp only [inclusion, change, FiniteFreeChartTransitions.ambientChange,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- The independently descended atlas map preserves every original line inclusion. -/
@[reassoc]
lemma reverse_square :
    LocallySplitLineAtlasSection.morphism s hL hs hM ≫ map a hM hN =
      LocallySplitLineAtlasSection.morphism (s ≫ a.hom) hL (hs.postcompose s a) hN := by
  apply (AffineFiniteFreeAtlas.cover M hM).hom_ext
  intro i
  change i.val.ι ≫ _ = i.val.ι ≫ _
  rw [LocallySplitLineAtlasSection.ι_morphism_assoc]
  change (point s hL hs i.val (chart M i) ≫
    LocallyFreeDualProjectiveAtlas.chartMap M hM i) ≫ _ = _
  rw [Category.assoc, chart_map, toAtlas, ← Category.assoc, point_chartIso]
  exact (LocallySplitLineAtlasSection.ι_morphism (s ≫ a.hom) hL
    (hs.postcompose s a) hN (index a i)).symm

/-- The geometric ambient morphism realizes the previously defined section transport. -/
lemma sectionChangeAmbient_val (s : DualAtlasLineQuotient.Section M hM) :
    (DualAtlasLineQuotient.sectionChangeAmbient a hM hN s).val = s.val ≫ map a hM hN := by
  let b := DualAtlasLineQuotient.fromSection M hM s
  have hr := reverse_square a hM hN b.inclusion b.rankOne b.locallySplit
  change (DualAtlasLineQuotient.toSection M hM b).val ≫ map a hM hN = _ at hr
  rw [DualAtlasLineQuotient.toSection_fromSection] at hr
  exact hr.symm

end FLT.Mazur.DualAtlasAmbient
