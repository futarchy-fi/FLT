/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertSchemeRestriction
public import FLT.Mazur.SchemeRelationRestrictionComposition
public import FLT.Mazur.RelativeRelationFullSectionFunctions

/-!
# Full original function equations on restricted quotient opens

Sections on an open of the restricted Hilbert quotient are exactly functions
compatible with the full ORIGINAL relation on its composite source immersion.
The comparison retains the original invariant-sheaf inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "p" => variableChartRelationFst f hL d V c
local notation "q" => variableChartRelationSnd f hL d V c
local notation "r" => fst f hL d V c k
local notation "s" => snd f hL d V c k

local notation "a" => equivalence f hL d V c k
variable (B : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))

/-- The actual source open above an open of the restricted quotient. -/
def restrictedSectionOpen : A.left.Opens := fullSectionSourceOpen a B

/-- The unchanged original source immersion on that open. -/
def restrictedSectionSource : (restrictedSectionOpen f hL d V c k B).toScheme ⟶
    (variableHilbertTest f d V).left := (restrictedSectionOpen f hL d V c k B).ι ≫ k.left

/-- Successive full restrictions retain exactly the original composite-source equations. -/
def restrictedSectionFunctionEquiv :
    compatibleFunctions
      (SchemeRelationRestriction.fst (p).left (q).left
        (restrictedSectionSource f hL d V c k B))
      (SchemeRelationRestriction.snd (p).left (q).left
        (restrictedSectionSource f hL d V c k B)) ≃+*
    compatibleFunctions
      (SchemeRelationRestriction.fst (r).left (s).left
        (restrictedSectionOpen f hL d V c k B).ι)
      (SchemeRelationRestriction.snd (r).left (s).left
        (restrictedSectionOpen f hL d V c k B).ι) :=
  (SchemeRelationRestriction.compositeFunctionEquiv (p).left (q).left k.left
    (restrictedSectionOpen f hL d V c k B).ι).trans
      (SchemeRelationRestriction.relationIsoFunctionEquiv
        (SchemeRelationRestriction.fst (p).left (q).left k.left)
        (SchemeRelationRestriction.snd (p).left (q).left k.left)
        (restrictedSectionOpen f hL d V c k B).ι (r).left (s).left
        (fullSchemeDoubleIso f hL d V c k)
        (fullSchemeDoubleIso_fst f hL d V c k) (fullSchemeDoubleIso_snd f hL d V c k))

/-- Every restricted quotient section is exactly a full original compatible source function. -/
def restrictedSectionOriginalEquiv : (invariantSheaf a).obj.obj (op B) ≃+*
    compatibleFunctions
      (SchemeRelationRestriction.fst (p).left (q).left
        (restrictedSectionSource f hL d V c k B))
      (SchemeRelationRestriction.snd (p).left (q).left
        (restrictedSectionSource f hL d V c k B)) :=
  (fullSectionFunctionEquiv a B).trans
    (restrictedSectionFunctionEquiv f hL d V c k B).symm

/-- This comparison is the original invariant inclusion in open-scheme section coordinates. -/
theorem restrictedSectionOriginalEquiv_val (v : (invariantSheaf a).obj.obj (op B)) :
    (restrictedSectionOriginalEquiv f hL d V c k B v).val =
      (fullSectionFunctionEquiv a B v).val := rfl

end FLT.Mazur.HilbertChart.AffineRestriction
