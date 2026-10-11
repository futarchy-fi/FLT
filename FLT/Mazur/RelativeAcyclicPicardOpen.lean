/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricAcyclicPicardSubfunctor

/-!
# Representing opens attached to actual relative Picard classes

Over a locally Noetherian proper flat family the simultaneous open depends
only on the relative class. The resulting actual open represents the
geometric acyclic Picard test condition on every cartesian test scheme.
It does not assert existence of a scheme representing the whole Picard functor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor properLineAcyclicRankOneOpen
variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- Every actual relative Picard class has a line-bundle representative. -/
theorem relativePic_exists_line (c : RelativePic f) :
    ∃ L : LineBundle X, relativeClass f (mk L.val L.property) = c := by
  obtain ⟨a, rfl⟩ := relativeClass_surjective f c
  induction a using inductionOn with
  | h L hL => exact ⟨⟨L, hL⟩, rfl⟩

variable [IsLocallyNoetherian S] [IsProper f] [Flat f]

/-- Relative-equivalent lines define the same actual open, including the rank-one condition. -/
theorem properLineAcyclicRankOneOpen_relativeClass {L M : X.Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M)
    (hc : relativeClass f (mk L hL) = relativeClass f (mk M hM)) :
    properLineAcyclicRankOneOpen f L hL = properLineAcyclicRankOneOpen f M hM := by
  obtain ⟨B, ⟨a⟩⟩ := (relativeClass_mk_eq_iff_twist_iso f hL hM).mp hc
  ext s
  change s ∈ properLineAcyclicRankOneOpen f L hL ↔
    s ∈ properLineAcyclicRankOneOpen f M hM
  rw [mem_properLineAcyclicRankOneOpen, mem_properLineAcyclicRankOneOpen]
  obtain ⟨b⟩ := baseLineTwist_fiber_iso f L B.property s
  let c := (Scheme.Modules.pullback (f.fiberι s)).mapIso a ≪≫ b
  exact (and_congr (forall_congr' fun n ↦
    Equiv.subsingleton_congr (moduleHIsoOfIso c (n + 1)).toEquiv)
      (congrArg (· = 1) (fiberSectionRank_eq_of_iso f s c)).to_iff).symm

/-- The actual open of a relative class, independent of the chosen line representative. -/
def relativeAcyclicPicardOpen (c : RelativePic f) : S.Opens :=
  let L := (relativePic_exists_line f c).choose
  properLineAcyclicRankOneOpen f L.val L.property

/-- On every line representative this is the existing simultaneous acyclic rank-one open. -/
theorem relativeAcyclicPicardOpen_mk (L : X.Modules) (hL : LocallyFreeRankOne L) :
    relativeAcyclicPicardOpen f (relativeClass f (mk L hL)) =
      properLineAcyclicRankOneOpen f L hL :=
  properLineAcyclicRankOneOpen_relativeClass f _ hL
    (relativePic_exists_line f (relativeClass f (mk L hL))).choose_spec

/-- Pullback of a relative class lies in the subfunctor precisely on this representing open. -/
theorem relativeAcyclicPicardOpen_represents {P T : Scheme.{0}}
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g)
    (c : RelativePic f) :
    RelativeGeometricAcyclicRankOne q (relativeMap q f p g h.w.symm c) ↔
      ∃! a : T ⟶ (relativeAcyclicPicardOpen f c).toScheme,
        a ≫ (relativeAcyclicPicardOpen f c).ι = g := by
  obtain ⟨L, rfl⟩ := relativePic_exists_line f c
  rw [relativeMap_class, pullback_mk, relativeGeometricAcyclicRankOne_mk,
    relativeAcyclicPicardOpen_mk]
  exact properLineAcyclicRankOneOpen_represents f L.val L.property h

/-- These class-defined representing opens commute with locally Noetherian base change. -/
theorem relativeAcyclicPicardOpen_baseChange {P T : Scheme.{0}} [IsLocallyNoetherian T]
    {p : P ⟶ X} {q : P ⟶ T} [IsProper q] [Flat q] {g : T ⟶ S}
    (h : IsPullback p q f g) (c : RelativePic f) :
    relativeAcyclicPicardOpen q (relativeMap q f p g h.w.symm c) =
      g ⁻¹ᵁ relativeAcyclicPicardOpen f c := by
  obtain ⟨L, rfl⟩ := relativePic_exists_line f c
  rw [relativeMap_class, pullback_mk, relativeAcyclicPicardOpen_mk,
    relativeAcyclicPicardOpen_mk]
  exact properLineAcyclicRankOneOpen_baseChange f L.val L.property h

end FLT.Mazur.CartierAbel
