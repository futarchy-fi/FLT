/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePicardClasses
public import FLT.Mazur.LineTrivializationCocycleRecovery
public import Mathlib.Logic.Small.Basic

/-!
# Small representatives for scheme Picard classes

A point-indexed trivializing open cover and its unit cocycle are small data.
Gluing these data recovers every actual line sheaf. Consequently the Picard
classes form a small type, without compactness or Noetherian hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemePicard
open FCurve
universe u
variable (X : Scheme.{u})

/-- Small gluing data for lines: an open cover indexed by the original points and units. -/
def LineCocycleCode : Type u :=
  Σ U : {U : X → X.Opens // iSup U = ⊤}, ModuleSheafUnitCocycle.Cocycle U.val

/-- The actual line obtained by gluing a small code. -/
def lineOfCocycleCode (c : LineCocycleCode X) : LineBundle X :=
  ⟨c.2.sheaf, c.2.locallyFreeRankOne c.1.property⟩

/-- Every line sheaf is recovered, up to actual isomorphism, from small gluing data. -/
theorem exists_line_cocycle_code (L : LineBundle X) :
    ∃ c : LineCocycleCode X, Nonempty ((lineOfCocycleCode X c).val ≅ L.val) := by
  choose U hx he using L.property
  let e x := Classical.choice (he x)
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  exact ⟨⟨⟨U, hU⟩, lineTrivializationCocycle e⟩, ⟨lineTrivializationCocycleIso e hU⟩⟩

/-- Mapping the small gluing codes to their Picard classes is surjective. -/
theorem cocycleCode_pic_surjective : Function.Surjective
    (fun c : LineCocycleCode X ↦
      mk (lineOfCocycleCode X c).val (lineOfCocycleCode X c).property) := by
  intro a
  induction a using inductionOn with | h M hM =>
    obtain ⟨c, ⟨e⟩⟩ := exists_line_cocycle_code X ⟨M, hM⟩
    exact ⟨c, mk_eq_of_iso _ _ e⟩

/-- Isomorphism classes of line sheaves on a small scheme form a small type. -/
instance smallPic : Small.{u} (Pic X) := small_of_surjective (cocycleCode_pic_surjective X)

end FLT.Mazur.SchemePicard
