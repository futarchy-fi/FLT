/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertOriginalOrbitOpenModel
public import FLT.Mazur.SchemeRelationSelectorEtale

/-!
# Constructed full original Picard models from arrow representatives

An invariant representative family on an original Hilbert selection constructs
its quotient scheme, its full kernel, and its etale surjective projection.
The original proper family and its unchanged ground are retained throughout.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
variable (r : A.left ⟶ (relation f hL d V c k).left)
local notation "i" => SchemeRelationSelectorQuotient.inclusion («q» := q) r

/-- The actual quotient scheme over the unchanged original family ground. -/
def selectorTarget : Over (Spec (.of R)) := Over.mk (i ≫ A.hom)

/-- Its representative inclusion is a morphism over the original ground. -/
def selectorInclusion : selectorTarget f hL d V c k r ⟶ A := Over.homMk i

/-- The quotient morphism is constructed, rather than supplied as an effectiveness premise. -/
def selectorProjection (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) :
    A ⟶ selectorTarget f hL d V c k r :=
  Over.homMk (SchemeRelationSelectorQuotient.projection r hr hi)
    (SchemeRelationSelectorQuotient.projection_ground r hr hi)

/-- The complete original Picard relation is the kernel of the constructed model. -/
theorem selectorProjection_isPullback (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) :
    IsPullback (p).left (q).left (selectorProjection f hL d V c k r hr hi).left
      (selectorProjection f hL d V c k r hr hi).left :=
  SchemeRelationSelectorQuotient.isPullback e r hr hi

/-- The quotient has a genuine section in original-family coordinates. -/
@[reassoc]
theorem selectorInclusion_projection (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) :
    selectorInclusion f hL d V c k r ≫ selectorProjection f hL d V c k r hr hi = 𝟙 _ :=
  Over.OverMorphism.ext (SchemeRelationSelectorQuotient.inclusion_projection r hr hi)

/-- Each original parameter is joined to its selected quotient representative. -/
theorem selector_representative_related (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) (x : A.left) :
    RelativeRelationOrbit.Related p q x
      ((selectorInclusion f hL d V c k r).left
        ((selectorProjection f hL d V c k r hr hi).left x)) := by
  refine ⟨r x, congrArg (fun a ↦ a x) hr, ?_⟩
  exact (congrArg (fun a ↦ a x)
    (SchemeRelationSelectorQuotient.projection_inclusion r hr hi)).symm

variable [Etale V.hom] [IsOpenImmersion k.left]

/-- The constructed full model is an etale surjection, with no coefficient-flatness input. -/
theorem selectorProjection_cover (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) :
    Etale (selectorProjection f hL d V c k r hr hi).left ∧
      Surjective (selectorProjection f hL d V c k r hr hi).left :=
  ⟨SchemeRelationSelectorQuotient.projection_etale e r hr hi,
    SchemeRelationSelectorQuotient.projection_surjective r hr hi⟩

end FLT.Mazur.HilbertChart.AffineRestriction
