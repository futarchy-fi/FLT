/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertSourceIntersection
public import FLT.Mazur.BaseOpenHilbertBaseChange
public import FLT.Mazur.SmoothHilbertInvariantQuotient

/-!
# Base-local translation neighborhoods in the original orbit quotient

The chart's source intersection is invariant under the original relation.
Its orbit image is therefore an actual quotient open, with precisely the
original open source intersection as inverse image. No coverage is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsOpenImmersion V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The actual source open defined by the base-local translated Hilbert chart. -/
def baseOpenSourceOpen : (smoothHilbertSource f).left.Opens :=
  (variableSourceInclusion f hL d V c).left.opensRange

/-- Membership in the source chart is unchanged along the original Picard relation. -/
theorem baseOpenSourceOpen_invariant :
    (smoothHilbertRelationFst f hL).left ⁻¹ᵁ baseOpenSourceOpen f hL d V c =
      (smoothHilbertRelationSnd f hL).left ⁻¹ᵁ baseOpenSourceOpen f hL d V c := by
  dsimp only [baseOpenSourceOpen, variableSourceInclusion]
  rw [baseOpenHilbert_preimage f hL, baseOpenHilbert_preimage f hL,
    smoothHilbertRelation_class]

/-- The source open with its proved invariance, not an assumed quotient chart. -/
def baseOpenInvariantSourceOpen :
    InvariantOpens (smoothHilbertRelationFst f hL) (smoothHilbertRelationSnd f hL) :=
  ⟨baseOpenSourceOpen f hL d V c, baseOpenSourceOpen_invariant f hL d V c⟩

/-- The concrete base-local chart determines an actual open of the orbit quotient. -/
def baseOpenOrbitOpen : Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) :=
  descendOpen (smoothHilbertEquivalenceRelation f hL) (baseOpenInvariantSourceOpen f hL d V c)

/-- The descended open has exactly the original chart intersection as source inverse image. -/
theorem baseOpenOrbitOpen_preimage :
    projection (smoothHilbertEquivalenceRelation f hL) ⁻¹' baseOpenOrbitOpen f hL d V c =
      (baseOpenSourceOpen f hL d V c : Set _) :=
  invariant_saturation (smoothHilbertEquivalenceRelation f hL)
    (baseOpenInvariantSourceOpen f hL d V c)

/-- A source point belongs to the quotient chart exactly when it belongs to the source chart. -/
theorem mem_baseOpenOrbitOpen_iff (x : (smoothHilbertSource f).left) :
    projection (smoothHilbertEquivalenceRelation f hL) x ∈ baseOpenOrbitOpen f hL d V c ↔
      x ∈ baseOpenSourceOpen f hL d V c :=
  Set.ext_iff.mp (baseOpenOrbitOpen_preimage f hL d V c) x

/-- The actual open source maps continuously into the descended quotient open. -/
def baseOpenSourceOrbitMap :
    C((variableSourceIntersection f hL d V c).left, baseOpenOrbitOpen f hL d V c) where
  toFun x := ⟨projection (smoothHilbertEquivalenceRelation f hL)
    ((variableSourceInclusion f hL d V c).left x),
    (mem_baseOpenOrbitOpen_iff f hL d V c _).mpr ⟨x, rfl⟩⟩
  continuous_toFun := (projection_continuous (smoothHilbertEquivalenceRelation f hL)).comp
    (variableSourceInclusion f hL d V c).left.continuous |>.subtype_mk _

/-- Every point of the descended open comes from the original source intersection. -/
theorem baseOpenSourceOrbitMap_surjective :
    Function.Surjective (baseOpenSourceOrbitMap f hL d V c) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, ⟨y, rfl⟩, hx⟩ := hz
  exact ⟨y, Subtype.ext hx⟩

end FLT.Mazur.HilbertChart
