/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertFaithfulClass

/-!
# Faithful-base affine sources still cover the original orbit quotient

The actual affine test cover supplies open orbit neighborhoods refining the
previous varying-chart cover. This is topological coverage; no scheme structure
on these orbit neighborhoods or full-envelope isomorphism is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertFaithfulOrbitCover
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertFaithfulTestCover
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL
local notation "e" => smoothHilbertEquivalenceRelation f hL

/-- The image of the actual refined affine source in the original orbit space. -/
def orbitOpen (x : (T).left) : TopologicalSpace.Opens (Orbit e) :=
  ⟨Set.range (projection e ∘ arrow f hL T s x),
    ((projection_isOpenMap e (smoothHilbertRelationSnd f hL).left.isOpenMap).comp
      (arrow f hL T s x).isOpenMap).isOpen_range⟩

/-- The original source point survives both refinements and lies in its new orbit open. -/
theorem projection_mem (x : (T).left) : projection e x ∈ orbitOpen f hL x := by
  refine ⟨(data f hL T s x).2.2.2.2, ?_⟩
  exact congrArg (projection e) (point_covers f hL T s x)

/-- The actual refined orbit neighborhood lies in the original ordered chart neighborhood. -/
theorem orbitOpen_le_original (x : (T).left) :
    orbitOpen f hL x ≤ OrderedHilbertAffineEtaleOrbitCover.orbitOpen f hL x := by
  rintro z ⟨a, rfl⟩
  apply (mem_smoothTranslationOrbitOpen_iff f hL _ _ _ (arrow f hL T s x a)).mpr
  exact ⟨(data f hL T s x).2.2.1 a, rfl⟩

/-- The refined faithful-base neighborhoods cover the entire ORIGINAL orbit quotient. -/
theorem covers : ⨆ x : (T).left, orbitOpen f hL x = ⊤ := by
  apply top_le_iff.mp
  intro z _
  obtain ⟨x, rfl⟩ := projection_surjective e z
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, projection_mem f hL x⟩

/-- Every original orbit has a point on one of the constructed affine sources. -/
theorem affine_source_covers (z : Orbit e) :
    ∃ (x : (T).left) (a : (data f hL T s x).2.1),
      projection e (arrow f hL T s x a) = z := by
  obtain ⟨x, rfl⟩ := projection_surjective e z
  exact ⟨x, (data f hL T s x).2.2.2.2, congrArg (projection e) (point_covers f hL T s x)⟩

end FLT.Mazur.OrderedHilbertFaithfulOrbitCover
