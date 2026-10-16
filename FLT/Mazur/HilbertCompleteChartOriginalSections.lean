/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteInteriorBoundaryLifts
public import FLT.Mazur.RelativeRelationEtaleSourceFunctions

/-!
# Descent of complete chart invariants to original orbit sections

Every invariant coefficient on a complete stable chart descends to one unique
section on its actual original orbit image. The equality is with the existing
geometric pullback equivalence, not an abstract identification of coefficient rings.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
variable (n : ℕ) (o : Fin n)
  (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
  EquivalenceRelationNormalizedFrames.source relativeFppfSheaf AmpleLineBundle
set_option quotPrecheck false
local notation "j" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "r" => SchemeRelationRestriction.fst p q j
local notation "s" => SchemeRelationRestriction.snd p q j
local notation "a" => SchemeRelationRestriction.arrow p q j
local notation "O" => orbitImageOpen eo (q).isOpenMap (etaleSourceImage j)

/-- Complete moving invariance is compatibility on the unchanged original double restriction. -/
theorem completeChart_original_compatible
    (hc : ∀ y : normalizedFullRelationFrames f hL d V c k n o,
      y ∈ U → y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (t : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n o) U hU)) :
    t.val ∈ SchemeEffectiveEpiSections.compatibleFunctions r s := by
  apply completeOpen_invariant_test e (Fin n) o U hU hc t r s a
  · simpa only [Category.assoc, normalizedFullRelationFirst] using
      SchemeRelationRestriction.arrow_fst p q j
  · simpa only [Category.assoc, normalizedFullRelationFirst] using
      SchemeRelationRestriction.arrow_snd p q j

/-- Every complete chart invariant is the pullback of a unique original orbit-image section. -/
theorem completeChart_original_section_existsUnique
    (hc : ∀ y : normalizedFullRelationFrames f hL d V c k n o,
      y ∈ U → y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (t : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n o) U hU)) :
    ∃! b : (invariantSheaf eo).obj.obj (op O),
      (etaleSourceFunctionEquiv eo (q).isOpenMap j b).val = t.val := by
  let v : SchemeEffectiveEpiSections.compatibleFunctions r s :=
    ⟨t.val, completeChart_original_compatible f hL d V c k n o U hU hc t⟩
  let E := etaleSourceFunctionEquiv eo (q).isOpenMap j
  refine ⟨E.symm v, congrArg Subtype.val (E.apply_symm_apply v), ?_⟩
  intro b hb
  apply E.injective
  exact (Subtype.ext hb).trans (E.apply_symm_apply v).symm

/-- Boundary chart lifts descend to actual original orbit-image sections with exact chart data. -/
theorem completeChart_original_boundary_section
    (hc : ∀ y : normalizedFullRelationFrames f hL d V c k n o,
      y ∈ U → y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (ha : IsAffineOpen U) (W : TopologicalSpace.Opens (Orbit eo))
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val)
    (t : (invariantSheaf ec).obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj W))) :
    ∃ b : (invariantSheaf eo).obj.obj (op O),
      ∃ v : invariantCoordinates (restrictedAction
        (normalizedFullRelationAction f hL d V c k n o) U hU),
        (etaleSourceFunctionEquiv eo (q).isOpenMap j b).val = v.val ∧
        normalizedBoundaryChartMap f hL d V c k n o U hU v =
          normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t := by
  obtain ⟨v, hv⟩ := normalizedOrbitBoundaryCoefficient_lift f hL d V c k n o W U hU hUW t ha
  obtain ⟨b, hb, _⟩ := completeChart_original_section_existsUnique f hL d V c k n o U hU hc v
  exact ⟨b, v, hb, hv⟩

end FLT.Mazur.HilbertChart.AffineRestriction
