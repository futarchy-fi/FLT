/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryParameterSections
public import FLT.Mazur.PolygonCompleteBoundaryFiberFrames
public import FLT.Mazur.PolygonCompleteBoundaryLabels

/-!
# Common boundary parameters on the original complete-family fiber

The actual finite relabeling acts on parameters for the original translated
boundary comparisons. The same comparisons retain the complete fiber's full
marking divisor, its section, and the original normalization and node maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation PolygonUniversalAction PolygonPinching
open CyclicBoundaryParameter CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translationIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (f : Over.mk g ⟶ CyclicBoundaryParameter.parameter (G K n) n) (j : Multiplicative (ZMod n))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "c" => markedSection (G K n) n g f (1, 1, j)
local notation "s" => g ≫ completeClosedBase K

/-- The actual complete-fiber comparison supplied by a cyclic boundary parameter test. -/
def completeCyclicBoundaryComparison :
    ((Over.pullback g).obj C).left ≅
      pullback (exactVeroneseProjToBase K n h) (s) :=
  completeMovedBoundaryFiberIso K n h g (c)

/-- Common relabeling retains the specified actual complete-fiber comparison. -/
theorem completeCyclicBoundaryComparison_action (e : RelabelGroup n) :
    completeCyclicBoundaryComparison K n h g (f ≫ (action (G K n) n e).hom) j =
      completeCyclicBoundaryComparison K n h g f (e.2.2.symm j) := by
  unfold completeCyclicBoundaryComparison
  rw [section_action_cyclic]

/-- The complete-family's original full marking pulls back to the entire moved product. -/
theorem completeCyclicBoundaryComparison_marking :
    (∏ i : Fin n, (completeFiberMarking K n h (s) i).ker).comap
      (completeCyclicBoundaryComparison K n h g f j).hom =
        movedProductMarkingIdeal K n hn p q hp g (c) (fun _ ↦ 1) :=
  completeFiberMarking_movedBoundary K n h g (c)

/-- The actual comparison retains the canonical section of the full original product. -/
theorem completeCyclicBoundaryComparison_section :
    DivisorLineSectionCompatible (completeCyclicBoundaryComparison K n h g f j).hom
      (completeFiberMarkingDivisor_relativeCartier K n h (s)).1
      (movedProductMarkingIdeal_cartier K n hn p q hp g (c) (fun _ ↦ 1)).1
      (completeBoundaryFiberLineIso K n h g (c)) :=
  completeBoundaryFiberLineIso_section K n h g (c)

/-- Every original complete-family marking is retained by the relabeled full comparison. -/
@[reassoc] theorem completeCyclicBoundaryComparison_originalMarking
    (e : RelabelGroup n) (i : Fin n) :
    completeMovedBoundaryMarking K n h g
        (markedSection (G K n) n g (f ≫ (action (G K n) n e).hom) (1, 1, j)) i ≫
      (completeCyclicBoundaryComparison K n h g
        (f ≫ (action (G K n) n e).hom) j).hom =
          completeFiberMarking K n h (s) i :=
  completeMovedBoundaryFiberIso_marking K n h g _ i

/-- Recovery of any original boundary map is invariant under the common action. -/
theorem completeCyclicBoundaryOriginalMap_action (e : RelabelGroup n)
    {X : Over (Spec (.of K))} (v : X ⟶ C) :
    completeBoundaryOriginalFiberMap K n h g
      (markedSection (G K n) n g (f ≫ (action (G K n) n e).hom) (1, 1, j)) v =
        completeBoundaryOriginalFiberMap K n h g (c) v :=
  completeBoundaryOriginalFiberMap_independent K n h g _ v (c)

/-- The original complete-fiber node frame itself follows the exact cyclic permutation. -/
theorem completeCyclicBoundaryNodeFrame_action (e : RelabelGroup n) (i : Fin n) :
    HEq (completeBoundaryFiberNodeLineIso K n h g
      (markedSection (G K n) n g (f ≫ (action (G K n) n e).hom) (1, 1, j)) i)
      (completeBoundaryFiberNodeLineIso K n h g
        (markedSection (G K n) n g f (1, 1, e.2.2.symm j)) i) := by
  rw [section_action_cyclic]

end FLT.Mazur.PolygonInfinitesimalStages
