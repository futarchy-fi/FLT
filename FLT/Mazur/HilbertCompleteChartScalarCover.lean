/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteChartScalarIso

/-!
# Finite faithfully flat coverage of complete-chart original scalar primes

The actual scalar morphism on a complete chart's own orbit image is a finite,
flat surjection. This includes every prime of that unchanged section ring,
with no reducedness or irreducibility assumption on the original parameter.
The assertion does not extend the scalar domain to a larger orbit open.
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
variable (n : ℕ) (o : Fin n)
  (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ g : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
  EquivalenceRelationNormalizedFrames.source relativeFppfSheaf AmpleLineBundle
local notation "j" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
set_option quotPrecheck false
local notation "O" => orbitImageOpen eo (q).isOpenMap (etaleSourceImage j)
local notation "E" => (pullOpen eo O).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op O)
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)

local notation "hUO" => normalizedChart_over_orbitImage f hL d V c k n o U
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o O U hU hUO
local notation "ρ" => restrictedAction τ U hU
local notation "σ₀" => invariantScalarCoordinates ρ σ
open SchemeScalarPrincipalNeighborhood

/-- Factor the original scalar morphism through the actual finite-group quotient. -/
theorem completeChart_scalarMorphism_factor :
    scalarMorphism σ₀ = quotientMap ρ ≫ Spec.map (CommRingCat.ofHom σ) := by
  change U.toScheme.toSpecΓ ≫ Spec.map _ =
    (U.toScheme.toSpecΓ ≫ Spec.map _) ≫ Spec.map _
  rw [Category.assoc, ← Spec.map_comp]
  rfl

/-- Completeness identifies the original scalar spectrum with the full chart quotient. -/
theorem completeChart_scalarSpec_isIso
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    IsIso (Spec.map (CommRingCat.ofHom σ)) := by
  let _ : IsIso (CommRingCat.ofHom σ) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (normalizedOriginalScalarMap_orbitImage_bijective f hL d V c k n o U hU hc)
  infer_instance

variable [IsAffine U.toScheme]

/-- Every prime of the original orbit-image scalar ring has an actual source point. -/
theorem completeChart_scalarMorphism_surjective
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    Surjective (scalarMorphism σ₀) := by
  rw [completeChart_scalarMorphism_factor]
  let _ := completeChart_scalarSpec_isIso f hL d V c k n o U hU hc
  infer_instance

/-- The original scalar morphism is finite; the source retains every branch and nilpotent. -/
theorem completeChart_scalarMorphism_finite
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    IsFinite (scalarMorphism σ₀) := by
  rw [completeChart_scalarMorphism_factor]
  let _ := completeChart_scalarSpec_isIso f hL d V c k n o U hU hc
  let _ := quotientMap_finite_of_free ρ
    (restrictedAction_free τ U hU (fun _ _ a g hg ↦ action_free e (Fin n) o a g hg))
  infer_instance

/-- The actual original scalar map is flat as a morphism of schemes. -/
theorem completeChart_scalarMorphism_flat
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    Flat (scalarMorphism σ₀) := by
  let _ : Flat (Spec.map (CommRingCat.ofHom σ₀)) := Flat.SpecMap_iff.mpr
    (completeChart_originalSource_flat f hL d V c k n o U hU hc)
  unfold scalarMorphism
  infer_instance

/-- Original scalar coverage and flatness together give a faithfully flat coordinate map. -/
theorem completeChart_originalSource_faithfullyFlat
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    (σ₀).FaithfullyFlat := by
  apply RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
  refine ⟨completeChart_originalSource_flat f hL d V c k n o U hU hc, ?_⟩
  have hs := completeChart_scalarMorphism_surjective f hL d V c k n o U hU hc
  intro P
  obtain ⟨x, hx⟩ := hs.surj P
  exact ⟨U.toScheme.toSpecΓ x, hx⟩

end FLT.Mazur.HilbertChart.AffineRestriction
