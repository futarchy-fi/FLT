/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameComparison
public import FLT.Mazur.EquivalenceRelationNormalizedFrameEtale

/-!
# Complete normalized lifts of original geometric endpoints

A complete ordered fiber contains the original identity arrow. Distinguishing
that label produces a normalized lift over the same endpoint, retaining every
original arrow. This supplies geometric lifts without claiming completeness
on any open neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I]

local instance normalizedLiftOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance normalizedLiftOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local notation "E" => Over.mk p
variable {K : Type} [Field K] {b : Spec (.of K) ⟶ A}
  (t : Over.mk b ⟶ distinctScheme (Over.mk p) I)
  (ht : Function.Bijective (fun i ↦ geometricCoordinate (Over.mk p) I t i default))

include ht in
/-- The full original identity arrow occurs in every complete geometric frame. -/
theorem exists_identity_coordinate :
    ∃ o : I, (t ≫ distinctCoordinate E I o).left = b ≫ e.r := by
  let r : Over.mk b ⟶ E := Over.homMk (b ≫ e.r) (by
    change (b ≫ e.r) ≫ p = b
    rw [Category.assoc, e.reflexivity₁, Category.comp_id])
  obtain ⟨o, ho⟩ := complete_coordinate_surjective E I t ht r
  exact ⟨o, congrArg Over.Hom.left ho⟩

variable (o : I) (h : b = (t ≫ distinctCoordinate (Over.mk p) I o).left ≫ q)

omit [Etale p] in
/-- The lifted test frame is the same original frame with its displayed base transported. -/
theorem testFrame_lift : testFrame I o (lift p q I o t h) =
    frameCast I (lift_first p q I o t h).symm t := by
  apply Over.OverMorphism.ext
  exact lift_inclusion p q I o t h

include ht in
omit [Etale p] in
/-- Normalizing a complete fiber does not discard any original geometric coordinate. -/
theorem lift_complete : Complete I o (lift p q I o t h) := by
  unfold Complete
  rw [testFrame_lift]
  exact frameCast_complete I (lift_first p q I o t h).symm t ht

variable [QuasiCompact p] [IsSepClosed K]
local instance normalizedLiftOver_quasiCompact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

include e in
/-- Every original geometric endpoint has a complete normalized lift of some finite size. -/
theorem exists_complete_normalized_lift (b : Spec (.of K) ⟶ A) :
    ∃ (n : ℕ) (o : Fin n) (u : Spec (.of K) ⟶ source p q (Fin n) o),
      u ≫ first p q (Fin n) o = b ∧ Complete (Fin n) o u := by
  obtain ⟨n, t, ht⟩ := exists_complete_geometric_tuple E b
  obtain ⟨o, ho⟩ := exists_identity_coordinate e (Fin n) t ht
  have h : b = (t ≫ distinctCoordinate E (Fin n) o).left ≫ q := by
    rw [ho, Category.assoc, e.reflexivity₂, Category.comp_id]
  exact ⟨n, o, lift p q (Fin n) o t h, lift_first p q (Fin n) o t h,
    lift_complete (Fin n) t ht o h⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
