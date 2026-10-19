/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRelatedPrincipalCharacters
public import FLT.Mazur.RelativeRelationMinimalScalarCharacters

/-!
# Minimal original scalar lifts supply full-character principal geometry

A minimal scalar lift constructs full-character neighborhoods in every related
fixed affine chart of the same size. Each neighborhood works over every
algebraically closed field and retains the exact original scalar morphism.
The principal denominator lies in the full invariant ring; coverage of an
entire prescribed scalar fiber is not asserted.
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
  {A : Over (Spec (.of R))} [IsAffine A.left] [IsLocallyNoetherian A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "s" => orbitScalarCoordinates eo W

attribute [local irreducible] invariantSheaf orbitScalarCoordinates
  scalarResidueClosureField scalarResidueClosureAlgebra
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete
  scalarMorphism finiteTargetOpen
local notation "K" P => scalarResidueClosure P

/-- Construct full-character principal neighborhoods from the actual minimal scalar lift. -/
theorem exists_minimal_scalar_principal_geometry (hW : IsAffineOpen E)
    (P : PrimeSpectrum Ω) (hP : P.asIdeal ∈ minimalPrimes Ω) :
    ∃ (b : Spec (.of (K P)) ⟶ (E).toScheme) (n : ℕ) (o : Fin n)
      (u : Spec (.of (K P)) ⟶ normalizedFullRelationFrames f hL d V c k n o),
      b ≫ scalarMorphism s = Spec.map (CommRingCat.ofHom (algebraMap Ω (K P))) ∧
      u ≫ normalizedFullRelationFirst f hL d V c k n o = b ≫ (E).ι ∧
      Complete (Fin n) o u ∧
      ∀ (o' : Fin n) (B : (normalizedFullRelationFrames f hL d V c k n o').Opens)
        (hB : ∀ g : Equiv.Perm (Fin n),
          (normalizedFullRelationAction f hL d V c k n o' g).hom ⁻¹ᵁ B = B)
        (_hBW : B ≤ normalizedFullRelationFirst f hL d V c k n o' ⁻¹ᵁ E)
        [IsAffine B.toScheme]
        (v : Spec (.of (K P)) ⟶ B.toScheme)
        (a : Spec (.of (K P)) ⟶ (relation f hL d V c k).left)
        (_ha : a ≫ p = u ≫ normalizedFullRelationFirst f hL d V c k n o)
        (_hb : a ≫ q = (v ≫ B.ι) ≫ normalizedFullRelationFirst f hL d V c k n o'),
      let ρ := restrictedAction (normalizedFullRelationAction f hL d V c k n o') B hB
      ∃ t : invariantCoordinates ρ,
        v default ∈ B.toScheme.basicOpen t.val ∧
        ∀ {F : Type} [Field F] [IsAlgClosed F]
          (χ : invariantCoordinates ρ →+* F), χ t ≠ 0 →
        ∃ w : Γ(B.toScheme, ⊤) →+* F,
          (∀ r : invariantCoordinates ρ, w r.val = χ r) ∧
          Complete (Fin n) o' (sourceCharacterMap w ≫ B.ι) ∧
          ∀ w' : Γ(B.toScheme, ⊤) →+* F,
            (∀ r : invariantCoordinates ρ, w' r.val = χ r) →
            Complete (Fin n) o' (sourceCharacterMap w' ≫ B.ι) ∧
            ∃! c' : Spec (.of F) ⟶ (relation f hL d V c k).left,
              c' ≫ p = (sourceCharacterMap w ≫ B.ι) ≫
                normalizedFullRelationFirst f hL d V c k n o' ∧
              c' ≫ q = (sourceCharacterMap w' ≫ B.ι) ≫
                normalizedFullRelationFirst f hL d V c k n o' := by
  obtain ⟨b, n, o, u, hb, hu, hc, hi⟩ := exists_minimal_scalar_complete_frame eo W P e hW
    (originalOrbitSource_scalar_finiteType f hL d V c k W hW) hP
  refine ⟨b, n, o, u, hb, hu, hc, ?_⟩
  intro o' B hB _hBW _ v a ha hb'
  obtain ⟨t, ht, hT⟩ := exists_related_principal_character_neighborhood
    f hL d V c k n o o' B hB u hi v a ha hb'
  refine ⟨t, ht, ?_⟩
  intro F _ _ χ hχ
  obtain ⟨w, hw, _, hcw, hall⟩ := hT χ hχ
  exact ⟨w, hw, hcw, hall⟩

end FLT.Mazur.HilbertChart.AffineRestriction
