/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundarySectionRotation
public import FLT.Mazur.PolygonStageRetainedRecovery
public import FLT.Mazur.SectionRetainedProjNaturality

/-!
# Canonical rotation of the original retained stage sections

Restrict the actual Cartier line pullback to the retained ring. Its inverse
comes from the negative label, and canonical stage recovery respects this map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules HomogeneousIdeal
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] family boundaryStageRetainedIso
  SectionGradedLinePullback.ringHom SectionRetainedLineEvaluation.map
  SectionRetainedProjConstruction.toProj Proj.map

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The rotation uses the canonical dual-ideal comparison on the original boundary line. -/
def boundaryRotationLineIso (m : ℕ) (a : ZMod n) :
    (pullback (stageRotation K n h m a)).obj (boundaryLine K m n h) ≅
      boundaryLine K m n h := by
  let _ : IsIso (idealModulePullbackHom (boundaryIdeal K m n h)
      (stageRotation K n h m a)) :=
    idealModulePullbackHom_isIso_of_cartier _ (boundaryIdeal_cartier K m n h).1
      ((boundaryIdeal_stageRotation K n h m a).symm ▸ (boundaryIdeal_cartier K m n h).1)
  exact divisorLinePullbackIsoOfEq _ (boundaryIdeal_cartier K m n h).1
    (boundaryIdeal_cartier K m n h).1 (boundaryIdeal_stageRotation K n h m a)

/-- Actual retained section pullback under the original rotation. -/
def boundaryRetainedRotation (m : ℕ) (a : ZMod n) :
    boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m →+*ᵍ
      boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m :=
  SectionRetainedLineEvaluation.map (stageRotation K n h m a)
    (boundaryLine K m n h) (boundaryLine K m n h)
    (boundaryRotationLineIso K n h m a) (exactVeroneseStep K n h)

/-- Restriction retains the actual full section-ring map, not a chosen substitute. -/
theorem boundaryRetainedRotation_val (m : ℕ) (a : ZMod n)
    (s : boundaryVeroneseRing K n h (exactVeroneseStep K n h) m) :
    (boundaryRetainedRotation K n h m a s).val =
      boundarySectionsRotation K n h m a s.val := by
  change (SectionRetainedLineEvaluation.map (stageRotation K n h m a)
    (boundaryLine K m n h) (boundaryLine K m n h)
    (boundaryRotationLineIso K n h m a) (exactVeroneseStep K n h) s).val = _
  rw [SectionRetainedLineEvaluation.map_val]
  rfl

attribute [local irreducible] boundaryLine boundaryRetainedRotation boundarySectionsRotation

/-- Zero rotation fixes the original retained stage ring. -/
@[simp] theorem boundaryRetainedRotation_zero (m : ℕ) :
    boundaryRetainedRotation K n h m 0 = GradedRingHom.id _ := by
  apply GradedRingHom.ext
  intro s
  apply Subtype.ext
  rw [boundaryRetainedRotation_val, boundarySectionsRotation_zero]
  rfl

/-- The actual retained pullbacks obey the cyclic addition law. -/
theorem boundaryRetainedRotation_add (m : ℕ) (a b : ZMod n) :
    boundaryRetainedRotation K n h m (a + b) =
      (boundaryRetainedRotation K n h m a).comp (boundaryRetainedRotation K n h m b) := by
  apply GradedRingHom.ext
  intro s
  apply Subtype.ext
  change (boundaryRetainedRotation K n h m (a + b) s).val =
    (boundaryRetainedRotation K n h m a (boundaryRetainedRotation K n h m b s)).val
  rw [boundaryRetainedRotation_val, boundaryRetainedRotation_val,
    boundaryRetainedRotation_val, boundarySectionsRotation_add]
  rfl

/-- Inverse rotation supplies every positive homogeneous section in the irrelevant image. -/
theorem boundaryRetainedRotation_irrelevant (m : ℕ) (a : ZMod n) :
    (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m)₊ ≤
      (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m)₊.map
        (boundaryRetainedRotation K n h m a) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (toIdeal_irrelevant_le _).mpr
  intro d hd s hs
  have hi : boundaryRetainedRotation K n h m a
      (boundaryRetainedRotation K n h m (-a) s) = s := by
    change ((boundaryRetainedRotation K n h m a).comp
      (boundaryRetainedRotation K n h m (-a))) s = s
    rw [← boundaryRetainedRotation_add, add_neg_cancel, boundaryRetainedRotation_zero]
    rfl
  rw [← hi]
  exact Ideal.mem_map_of_mem _
    (mem_irrelevant_of_mem _ hd ((boundaryRetainedRotation K n h m (-a)).map_mem hs))

/-- Original stage recovery intertwines the geometric rotation and its retained section map. -/
@[reassoc] theorem boundaryStageRetainedIso_rotation (m : ℕ) (a : ZMod n) :
    (boundaryStageRetainedIso K n h m).hom ≫
        Proj.map (boundaryRetainedRotation K n h m a)
          (boundaryRetainedRotation_irrelevant K n h m a) =
      stageRotation K n h m a ≫ (boundaryStageRetainedIso K n h m).hom := by
  rw [boundaryStageRetainedIso_hom]
  have hir := boundaryRetainedRotation_irrelevant K n h m a
  unfold boundaryRetainedRotation at hir ⊢
  exact SectionRetainedProjNaturality.toProj_map (stageRotation K n h m a)
    (boundaryLine K m n h) (boundaryLine K m n h)
    (boundaryRotationLineIso K n h m a) (exactVeroneseStep K n h)
    (boundaryExactRetainedGenerated K n h m) (boundaryExactRetainedGenerated K n h m)
    hir

end FLT.Mazur.PolygonInfinitesimalStages
