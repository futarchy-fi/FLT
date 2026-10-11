/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierBoundarySectionRingIdentity
public import FLT.Mazur.PolygonInfinitesimalRotationDivisor
public import FLT.Mazur.PolygonInfinitesimalStageRotation
public import FLT.Mazur.PolygonSectionRingFunctor

/-!
# Cyclic pullback on the actual boundary section rings

The proved invariant boundary ideal gives canonical pullback on all tensor
degrees. These ring maps commute with every original stage restriction and
satisfy the cyclic action laws, without choosing replacement line comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original stage rotation preserves the whole original boundary ideal. -/
theorem boundaryIdeal_stageRotation (m : ℕ) (a : ZMod n) :
    (boundaryIdeal R m n h).comap (stageRotation R n h m a) = boundaryIdeal R m n h :=
  unitMarkingDivisor_rotation (Ring R m) (parameter R m) n h a

/-- The actual rotation pulls back every section of every boundary tensor power. -/
def boundarySectionsRotation (m : ℕ) (a : ZMod n) :
    boundaryGradedSections R n h m →+* boundaryGradedSections R n h m :=
  cartierSectionRingMap (stageRotation R n h m a)
    (boundaryIdeal_cartier R m n h).1 (boundaryIdeal_cartier R m n h).1
    (boundaryIdeal_stageRotation R n h m a)

/-- The cyclic pullback preserves every original homogeneous tensor degree. -/
theorem boundarySectionsRotation_mem_grade (m : ℕ) (a : ZMod n) (d : ℕ)
    {s : boundaryGradedSections R n h m}
    (hs : s ∈ SectionGradedSum.grade (boundaryLine R m n h) ⊤ d) :
    boundarySectionsRotation R n h m a s ∈
      SectionGradedSum.grade (boundaryLine R m n h) ⊤ d :=
  cartierSectionRingMap_mem_grade _ _ _ _ d hs

/-- Rotation commutes with all the specified original boundary section restrictions. -/
theorem boundarySectionsRotation_naturality (a : ZMod n) {k l : ℕ} (f : k ⟶ l) :
    (boundarySectionsMap R n h f).comp (boundarySectionsRotation R n h l a) =
      (boundarySectionsRotation R n h k a).comp (boundarySectionsMap R n h f) := by
  exact cartierSectionRingMap_square
    ((stageSystem R n h).map f) (stageRotation R n h l a)
    (stageRotation R n h k a) ((stageSystem R n h).map f)
    ((systemRotation R n h a).naturality f)
    (boundaryIdeal_cartier R l n h).1 (boundaryIdeal_cartier R l n h).1
    (boundaryIdeal_cartier R k n h).1 (boundaryIdeal_cartier R k n h).1
    (boundaryIdeal_stageRotation R n h l a) (boundaryIdeal_systemMap R n h f)
    (boundaryIdeal_systemMap R n h f) (boundaryIdeal_stageRotation R n h k a)

/-- Zero rotation fixes every actual boundary section. -/
@[simp] theorem boundarySectionsRotation_zero (m : ℕ) :
    boundarySectionsRotation R n h m 0 = RingHom.id _ := by
  unfold boundarySectionsRotation
  have hz : stageRotation R n h m 0 = 𝟙 _ :=
    rotation_zero (Ring R m) (parameter R m) n h
  simp only [hz]
  exact cartierSectionRingMap_id _ _ _

/-- Addition of labels is the composite of the canonical section pullbacks. -/
theorem boundarySectionsRotation_add (m : ℕ) (a b : ZMod n) :
    boundarySectionsRotation R n h m (a + b) =
      (boundarySectionsRotation R n h m a).comp (boundarySectionsRotation R n h m b) := by
  have hab : stageRotation R n h m (a + b) =
      stageRotation R n h m a ≫ stageRotation R n h m b :=
    rotation_add (Ring R m) (parameter R m) n h a b
  unfold boundarySectionsRotation
  simp only [hab]
  exact cartierSectionRingMap_comp _ _ _ _ _ _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
