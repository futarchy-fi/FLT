/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceConstructedOpenSections
public import FLT.Mazur.SchemeRelationNoetherianRestriction

/-!
# Noetherianity of the actual Hilbert source and its full restricted relation

Derive both Noetherian instances from the original finite-type family and
the chosen affine source open. The full double relation remains unrestricted
and need not be affine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS
/-- The chosen affine normalized source is Noetherian over the original family. -/
theorem originalSource_affine_isNoetherian (ha : IsAffineOpen U) :
    IsNoetherian U.toScheme := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := LocallyOfFiniteType.isLocallyNoetherian
    (normalizedFullRelationFirst f hL d V c k n o)
  let _ := isLocallyNoetherian_of_isOpenImmersion U.ι
  let _ : IsAffine U.toScheme := ha
  exact ⟨⟩

/-- Both independent endpoints give a Noetherian full relation on this actual chart. -/
theorem originalSource_doubleRelation_isNoetherian (ha : IsAffineOpen U) :
    IsNoetherian D := by
  let _ := originalSource_affine_isNoetherian f hL d V c k n o U ha
  exact SchemeRelationRestriction.doubleDomain_isNoetherian p q kS

end FLT.Mazur.HilbertChart.AffineRestriction
