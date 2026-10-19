/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSpecializationOriginalScalarGeometry
public import FLT.Mazur.EquivalenceRelationComponentPrincipalBranches

/-!
# Reducible fixed Hilbert charts and constructed original scalar branches

Component anchors cover all full characters on the fixed chart. On an
individual anchored component, the original scalar image has exact complete
lifts. With a Noetherian original scalar ring, finite type constructs principal
coverage along each minimal contracted source branch; Noetherianity is an
explicit additional hypothesis, not inferred from the source alone.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
open RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
variable (n : ℕ) (o : Fin n)
  (B : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hB : ∀ g : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ B = B)
  (hBW : B ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
  [IsAffine B.toScheme]
local notation "ρ" => restrictedAction (normalizedFullRelationAction f hL d V c k n o) B hB
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W B hB hBW
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "s" => invariantScalarCoordinates ρ σ
local notation "u" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
local notation "K" P => scalarResidueClosure P
attribute [local irreducible] invariantSheaf normalizedOriginalScalarMap
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete scalarMorphism
  scalarResidueClosureField scalarResidueClosureAlgebra
  EquivalenceRelationNormalizedFrames.action restrictedAction

/-- Anchors on all components give every full character on the fixed reducible chart. -/
theorem exists_fixed_component_covered_character
    (hanchors : ∀ Z ∈ irreducibleComponents (quotient ρ),
      ∃ x : B.toScheme, B.ι x ∈ completeInterior («p» := p) («q» := q) (Fin n) o ∧
        quotientMap ρ x ∈ Z)
    {F : Type} [Field F] [IsAlgClosed F] (χ : invariantCoordinates ρ →+* F) :
    ∃ w : Γ(B.toScheme, ⊤) →+* F,
      (∀ r : invariantCoordinates ρ, w r.val = χ r) ∧ Complete (Fin n) o (u w) ∧
      ∀ v : Γ(B.toScheme, ⊤) →+* F,
        (∀ r : invariantCoordinates ρ, v r.val = χ r) → Complete (Fin n) o (u v) ∧
        ∃! a : Spec (.of F) ⟶ (relation f hL d V c k).left,
          a ≫ p = (u w) ≫ normalizedFullRelationFirst f hL d V c k n o ∧
          a ≫ q = (u v) ≫ normalizedFullRelationFirst f hL d V c k n o := by
  apply exists_complete_closed_character e (Fin n) o B hB χ
  obtain ⟨y, hy⟩ := (quotientMap ρ).surjective (PrimeSpectrum.comap χ ⊥)
  exact ⟨y, complete_fixed_chart_of_component_anchors e (Fin n) o B hB hanchors y, hy⟩

/-- Every scalar prime in an anchored closed component's image has exact complete geometry. -/
theorem exists_original_component_scalar_geometry
    (Z : Set (quotient ρ)) (hZ : IsPreirreducible Z) (hclosed : IsClosed Z)
    (x : B.toScheme) (hx : B.ι x ∈ completeInterior («p» := p) («q» := q) (Fin n) o)
    (hxZ : quotientMap ρ x ∈ Z) (P : PrimeSpectrum Ω)
    (hP : P ∈ PrimeSpectrum.comap σ '' Z) :
    ∃ w : Γ(B.toScheme, ⊤) →+* K P,
      w.comp s = algebraMap Ω (K P) ∧ Complete (Fin n) o (u w) ∧
      quotientMap ρ (sourceCharacterMap w default) ∈ Z ∧
      sourceCharacterMap w ≫ scalarMorphism s =
        Spec.map (CommRingCat.ofHom (algebraMap Ω (K P))) := by
  exact exists_complete_component_scalar_character e (Fin n) o B hB σ
    (normalizedChart_prescribedScalar_finiteType f hL d V c k W n o B hB hBW)
    Z hZ hclosed x hx hxZ P hP

local notation "i" => invariantScalarCoordinates ρ (RingHom.id (invariantCoordinates ρ))

/-- Construct principal scalar coverage without a supplied scalar-image witness. -/
theorem exists_original_component_principal_geometry [IsNoetherianRing Ω]
    (Z : Set (quotient ρ)) (hZ : IsPreirreducible Z) (hclosed : IsClosed Z)
    (x : B.toScheme) (hx : B.ι x ∈ completeInterior («p» := p) («q» := q) (Fin n) o)
    (hxZ : quotientMap ρ x ∈ Z) (P : PrimeSpectrum Ω)
    (hP : P.asIdeal ∈ (((PrimeSpectrum.vanishingIdeal Z).map i).comap s).minimalPrimes) :
    ∃ t : Ω, t ∉ P.asIdeal ∧ ∀ Q : PrimeSpectrum Ω,
      P.asIdeal ≤ Q.asIdeal → t ∉ Q.asIdeal →
      ∃ w : Γ(B.toScheme, ⊤) →+* K Q,
        w.comp s = algebraMap Ω (K Q) ∧ Complete (Fin n) o (u w) ∧
        quotientMap ρ (sourceCharacterMap w default) ∈ Z ∧
        sourceCharacterMap w ≫ scalarMorphism s =
          Spec.map (CommRingCat.ofHom (algebraMap Ω (K Q))) := by
  let g := (Ideal.Quotient.mk ((PrimeSpectrum.vanishingIdeal Z).map i)).comp s
  have ht : g.FiniteType :=
    (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp
      (normalizedChart_prescribedScalar_finiteType f hL d V c k W n o B hB hBW)
  have hp : g.FinitePresentation := by
    let _ := g.toAlgebra
    exact Algebra.FinitePresentation.of_finiteType.mp ht
  exact exists_complete_component_principal_branch e (Fin n) o B hB σ
    Z hZ hclosed x hx hxZ hp P hP

end FLT.Mazur.HilbertChart.AffineRestriction
