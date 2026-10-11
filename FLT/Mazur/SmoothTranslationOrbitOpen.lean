/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertIntersectionBaseChange
public import FLT.Mazur.VariableHilbertSourceIntersection
public import FLT.Mazur.SmoothHilbertInvariantQuotient

/-!
# Actual quotient neighborhoods from smooth translation bases

The image of a variable chart in the original source is open and invariant.
It therefore descends to an actual open of the original invariant quotient.
The smooth source intersection need not embed in the source, and the parameter
scheme need not be isomorphic to this quotient neighborhood.
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
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

instance variableSourceInclusion_smooth : Smooth (variableSourceInclusion f hL d V c).left :=
  variableHilbertOverlapToTest_smooth f d V c _ _

/-- The actual open image of the smooth chart intersection in the original source. -/
def smoothTranslationSourceOpen : (smoothHilbertSource f).left.Opens :=
  ⟨Set.range (variableSourceInclusion f hL d V c).left,
    (variableSourceInclusion f hL d V c).left.isOpenMap.isOpen_range⟩

/-- Smooth chart images are invariant under the complete original relation. -/
theorem smoothTranslationSourceOpen_invariant :
    (smoothHilbertRelationFst f hL).left ⁻¹ᵁ smoothTranslationSourceOpen f hL d V c =
      (smoothHilbertRelationSnd f hL).left ⁻¹ᵁ smoothTranslationSourceOpen f hL d V c := by
  apply Opens.ext
  change (smoothHilbertRelationFst f hL).left ⁻¹'
      Set.range (variableHilbertOverlapToTest f d V c _ _).left =
    (smoothHilbertRelationSnd f hL).left ⁻¹'
      Set.range (variableHilbertOverlapToTest f d V c _ _).left
  rw [variableHilbertBaseChange_range f hL, variableHilbertBaseChange_range f hL,
    smoothHilbertRelation_class]

/-- The image with its proved original-relation invariance. -/
def smoothTranslationInvariantSourceOpen :
    InvariantOpens (smoothHilbertRelationFst f hL) (smoothHilbertRelationSnd f hL) :=
  ⟨smoothTranslationSourceOpen f hL d V c,
    smoothTranslationSourceOpen_invariant f hL d V c⟩

/-- A smooth translation determines an actual open in the original quotient. -/
def smoothTranslationOrbitOpen : Opens (Orbit (smoothHilbertEquivalenceRelation f hL)) :=
  descendOpen (smoothHilbertEquivalenceRelation f hL)
    (smoothTranslationInvariantSourceOpen f hL d V c)

/-- Its source inverse image is exactly the smooth intersection image. -/
theorem smoothTranslationOrbitOpen_preimage :
    projection (smoothHilbertEquivalenceRelation f hL) ⁻¹'
      smoothTranslationOrbitOpen f hL d V c =
        (smoothTranslationSourceOpen f hL d V c : Set _) :=
  invariant_saturation (smoothHilbertEquivalenceRelation f hL)
    (smoothTranslationInvariantSourceOpen f hL d V c)

/-- Orbit membership is detected on the actual original source. -/
theorem mem_smoothTranslationOrbitOpen_iff (x : (smoothHilbertSource f).left) :
    projection (smoothHilbertEquivalenceRelation f hL) x ∈
      smoothTranslationOrbitOpen f hL d V c ↔
        x ∈ smoothTranslationSourceOpen f hL d V c :=
  Set.ext_iff.mp (smoothTranslationOrbitOpen_preimage f hL d V c) x

/-- The common source maps continuously into the actual quotient neighborhood. -/
def smoothTranslationSourceOrbitMap :
    C((variableSourceIntersection f hL d V c).left,
      smoothTranslationOrbitOpen f hL d V c) where
  toFun x := ⟨projection (smoothHilbertEquivalenceRelation f hL)
    ((variableSourceInclusion f hL d V c).left x),
    (mem_smoothTranslationOrbitOpen_iff f hL d V c _).mpr ⟨x, rfl⟩⟩
  continuous_toFun := (projection_continuous (smoothHilbertEquivalenceRelation f hL)).comp
    (variableSourceInclusion f hL d V c).left.continuous |>.subtype_mk _

/-- Every orbit in the neighborhood lifts to the common source. -/
theorem smoothTranslationSourceOrbitMap_surjective :
    Function.Surjective (smoothTranslationSourceOrbitMap f hL d V c) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, ⟨y, rfl⟩, hx⟩ := hz
  exact ⟨y, Subtype.ext hx⟩

/-- The common source gives an open map onto the actual quotient neighborhood. -/
theorem smoothTranslationSourceOrbitMap_isOpenMap :
    IsOpenMap (smoothTranslationSourceOrbitMap f hL d V c) :=
  ((projection_isOpenMap (smoothHilbertEquivalenceRelation f hL)
    (smoothHilbertRelationSnd f hL).left.isOpenMap).comp
      (variableSourceInclusion f hL d V c).left.isOpenMap).codRestrict _

end FLT.Mazur.HilbertChart
