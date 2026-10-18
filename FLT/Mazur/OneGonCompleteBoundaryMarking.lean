/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteBoundaryCartesian
public import FLT.Mazur.PolygonParameterMarkingLine

/-!
# The complete one-gon's original marking over varying boundary parameters

The actual complete infinity ideal pulls back to the original one-gon marking,
then to its full translated ideal over every parameter scheme. Its canonical
line comparison preserves the section and retains relative ampleness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OneGonSmoothing
open PolygonParameterTranslation PolygonMarkingBaseChange PolygonUniversalAction FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal movedMarkingIdeal
variable (K : Type) [Field K]
local notation "C" => OneGonNormalization.polygon K
local notation "p" => OneGonNormalization.normalizationOver K
local notation "q" => OneGonNormalization.nodes K
local notation "h" => OneGonGlobalPushout.isPushout K (by decide)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "b" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))

/-- The original labeled one-gon marking retains the complete family's actual infinity section. -/
@[reassoc] theorem boundaryClosedMap_marking (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (p) 1 i ≫ boundaryClosedMap K =
      (b) ≫ marking (t) := by
  rw [boundaryClosedMap, original_marking_closedFiber_assoc, fiberMarking_fst]

/-- The full complete marking ideal recovers the original closed one-gon marking. -/
theorem boundaryClosedMap_ideal (i : Fin 1) :
    (marking (t)).ker.comap (boundaryClosedMap K) =
      (PolygonMarkedSections.sectionMap K 1 (p) 1 i).ker := by
  let _ := family_proper (t)
  exact section_ker_comap_of_cartesian (boundaryClosed_isPullback K)
    (PolygonMarkedSections.sectionMap K 1 (p) 1 i) (marking (t))
    (PolygonMarkedSections.section_base K 1 (p) 1 i) (marking_toBase (t))
    (boundaryClosedMap_marking K i)

variable {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K 1))

/-- The entire original marking ideal is retained on every boundary parameter scheme. -/
theorem boundaryParameterMap_ideal :
    (marking (t)).ker.comap (boundaryParameterMap K g) = markingIdeal K 1 (p) g 1 0 := by
  rw [boundaryParameterMap, Scheme.IdealSheafData.comap_comp, boundaryClosedMap_ideal K 0,
    markingIdeal]

/-- The complete one-gon marking recovers the full ideal translated by the actual group section. -/
theorem boundaryMovedMap_ideal :
    (marking (t)).ker.comap (boundaryMovedMap K g c) =
      movedMarkingIdeal K 1 (by decide) (p) (q) (h) g c 1 0 := by
  rw [boundaryMovedMap, Scheme.IdealSheafData.comap_comp, boundaryParameterMap_ideal,
    movedMarkingIdeal]

/-- The canonical complete marking line on the actual translated one-gon. -/
irreducible_def boundaryMovedLineIso :
    (Scheme.Modules.pullback (boundaryMovedMap K g c)).obj (markingLine (t)) ≅
      movedMarkingLine K 1 (by decide) (p) (q) (h) g c 1 0 := by
  let hs := (marking_relativeCartier (t)).1
  let ht := (movedMarkingIdeal_cartier K 1 (by decide) (p) (q) (h) g c 1 0).1
  let he := boundaryMovedMap_ideal K g c
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The original complete one-gon comparison preserves its canonical vanishing section. -/
theorem boundaryMovedLineIso_section :
    DivisorLineSectionCompatible (boundaryMovedMap K g c) (marking_relativeCartier (t)).1
      (movedMarkingIdeal_cartier K 1 (by decide) (p) (q) (h) g c 1 0).1
      (boundaryMovedLineIso K g c) := by
  let hs := (marking_relativeCartier (t)).1
  let ht := (movedMarkingIdeal_cartier K 1 (by decide) (p) (q) (h) g c 1 0).1
  let he := boundaryMovedMap_ideal K g c
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [boundaryMovedLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The complete family's ampleness is retained on the whole original translated one-gon. -/
theorem boundaryMovedMarking_relativelyAmple :
    RelativelyAmpleLineBundle ((Over.pullback g).obj C).hom
      (movedMarkingLine K 1 (by decide) (p) (q) (h) g c 1 0) := by
  let _ := family_proper (t)
  exact ((completeMarkingLine_relativelyAmple K).of_isPullback
    (boundaryMoved_isPullback K g c)).of_iso (boundaryMovedLineIso K g c).symm

end FLT.Mazur.OneGonSmoothing
