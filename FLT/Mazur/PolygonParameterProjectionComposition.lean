/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalChartRestriction
public import FLT.Mazur.PolygonSmoothingRingMapComposition

/-!
# Composition on the full infinitesimal polygon atlas

The original parameter projections satisfy the identity and composition laws
by checking every chart of the cyclic cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
universe u
set_option backward.isDefEq.respectTransparency false
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Identity coefficient change fixes the whole original glued family. -/
theorem parameterProjection_id (t : R) [Fact (IsNilpotent t)] (n : ℕ) (h : 2 ≤ n) :
    parameterProjection (RingHom.id R) t t rfl n h = 𝟙 _ := by
  apply (chartCover R t n h).hom_ext
  intro i
  change chart R t n h i ≫ _ = chart R t n h i ≫ _
  rw [chart_parameterProjection, ringMap_id]
  simp only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]

/-- The actual glued coefficient projections compose on every original chart. -/
@[reassoc] theorem parameterProjection_comp (f : R →+* S) (g : S →+* T)
    (t : R) (s : S) (r : T)
    [Fact (IsNilpotent t)] [Fact (IsNilpotent s)] [Fact (IsNilpotent r)]
    (hs : f t = s) (hr : g s = r) (n : ℕ) (h : 2 ≤ n) :
    parameterProjection g s r hr n h ≫ parameterProjection f t s hs n h =
      parameterProjection (g.comp f) t r (by rw [RingHom.comp_apply, hs, hr]) n h := by
  apply (chartCover T r n h).hom_ext
  intro i
  change chart T r n h i ≫ _ = chart T r n h i ≫ _
  rw [chart_parameterProjection_assoc, chart_parameterProjection,
    chart_parameterProjection, ← Category.assoc, ← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp, ringMap_comp]

end FLT.Mazur.PolygonInfinitesimal
