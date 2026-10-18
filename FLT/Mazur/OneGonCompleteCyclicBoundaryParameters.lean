/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteBoundaryMarking
public import FLT.Mazur.CyclicBoundaryParameterSections

/-!
# Actual cyclic boundary parameters for the complete one-gon smoothing

Cyclic parameter tests give comparisons with the actual complete one-gon
fiber. Common finite relabeling preserves these comparisons, their full
marking ideals, canonical sections, and relative ampleness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OneGonSmoothing
open PolygonParameterTranslation PolygonUniversalAction CyclicBoundaryParameter FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (f : Over.mk g ⟶ parameter (G K 1) n) (j : Multiplicative (ZMod n))
local notation "C" => OneGonNormalization.polygon K
local notation "p" => OneGonNormalization.normalizationOver K
local notation "q" => OneGonNormalization.nodes K
local notation "h" => OneGonGlobalPushout.isPushout K (by decide)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "b" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))
local notation "c" => markedSection (G K 1) n g f (1, 1, j)

/-- The actual complete one-gon fiber comparison supplied by a cyclic boundary test. -/
def boundaryCyclicComparison :
    ((Over.pullback g).obj C).left ≅ pullback (family (t)).hom (g ≫ (b)) :=
  boundaryMovedFiberIso K g (c)

/-- Common finite relabeling retains the whole original one-gon comparison. -/
theorem boundaryCyclicComparison_action (e : CyclicCharacteristicAtlas.RelabelGroup n) :
    boundaryCyclicComparison K n g (f ≫ (action (G K 1) n e).hom) j =
      boundaryCyclicComparison K n g f (e.2.2.symm j) := by
  unfold boundaryCyclicComparison
  rw [section_action_cyclic]

/-- The actual complete fiber marking pulls back to the full original translated ideal. -/
theorem boundaryCyclicComparison_ideal :
    (fiberMarking (t) (g ≫ (b))).ker.comap
      (boundaryCyclicComparison K n g f j).hom =
        movedMarkingIdeal K 1 (by decide) (p) (q) (h) g (c) 1 0 := by
  rw [← marking_ker_comap, ← Scheme.IdealSheafData.comap_comp,
    boundaryCyclicComparison, boundaryMovedFiberIso_fst, boundaryMovedMap_ideal]

/-- The actual complete-fiber marking line on the whole original one-gon. -/
irreducible_def boundaryCyclicLineIso :
    (Scheme.Modules.pullback (boundaryCyclicComparison K n g f j).hom).obj
      (fiberMarkingLine (t) (g ≫ (b))) ≅
        movedMarkingLine K 1 (by decide) (p) (q) (h) g (c) 1 0 := by
  let hs := (fiberMarking_relativeCartier (t) (g ≫ (b))).1
  let ht := (movedMarkingIdeal_cartier K 1 (by decide) (p) (q) (h) g (c) 1 0).1
  let he := boundaryCyclicComparison_ideal K n g f j
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The one-gon cyclic boundary comparison retains the complete marking's canonical section. -/
theorem boundaryCyclicLineIso_section :
    DivisorLineSectionCompatible (boundaryCyclicComparison K n g f j).hom
      (fiberMarking_relativeCartier (t) (g ≫ (b))).1
      (movedMarkingIdeal_cartier K 1 (by decide) (p) (q) (h) g (c) 1 0).1
      (boundaryCyclicLineIso K n g f j) := by
  let hs := (fiberMarking_relativeCartier (t) (g ≫ (b))).1
  let ht := (movedMarkingIdeal_cartier K 1 (by decide) (p) (q) (h) g (c) 1 0).1
  let he := boundaryCyclicComparison_ideal K n g f j
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [boundaryCyclicLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The complete smoothing's ample marking is retained under the same finite relabeling. -/
theorem boundaryCyclicMarking_action_ample (e : CyclicCharacteristicAtlas.RelabelGroup n) :
    RelativelyAmpleLineBundle ((Over.pullback g).obj C).hom
      (movedMarkingLine K 1 (by decide) (p) (q) (h) g
        (markedSection (G K 1) n g (f ≫ (action (G K 1) n e).hom) (1, 1, j)) 1 0) := by
  rw [section_action_cyclic]
  exact boundaryMovedMarking_relativelyAmple K g _

end FLT.Mazur.OneGonSmoothing
