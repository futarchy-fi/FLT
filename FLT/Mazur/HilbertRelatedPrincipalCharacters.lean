/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRelatedFixedScalarCharts
public import FLT.Mazur.EquivalenceRelationPrincipalCompleteCharacters
public import FLT.Mazur.SchemeScalarGeometricOpenLift

/-!
# Full-character neighborhoods in independently fixed related Hilbert charts

The actual original arrow supplies the interior point. A constructed invariant
denominator then controls every full character in a principal neighborhood of
the fixed affine chart. Arrows between full-character lifts are constructed;
original scalar compatibility follows by restricting the full characters.
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

variable (n : ℕ) (o o' : Fin n)
  (B : (normalizedFullRelationFrames f hL d V c k n o').Opens)
  (hB : ∀ g : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o' g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
local notation "ρ" => restrictedAction (normalizedFullRelationAction f hL d V c k n o') B hB
local notation "lifted" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
attribute [local irreducible] invariantSheaf normalizedOriginalScalarMap
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete scalarMorphism
  EquivalenceRelationNormalizedFrames.action restrictedAction invariantScalarCoordinates
  sourceCharacterMap

/-- A related fixed chart has a constructed neighborhood controlling all full characters. -/
theorem exists_related_principal_character_neighborhood {K : Type} [Field K]
    (u : Spec (.of K) ⟶ normalizedFullRelationFrames f hL d V c k n o)
    (hi : u default ∈ completeInterior («p» := p) («q» := q) (Fin n) o)
    (v : Spec (.of K) ⟶ B.toScheme) (a : Spec (.of K) ⟶ (relation f hL d V c k).left)
    (ha : a ≫ p = u ≫ normalizedFullRelationFirst f hL d V c k n o)
    (hb : a ≫ q = (v ≫ B.ι) ≫ normalizedFullRelationFirst f hL d V c k n o') :
    ∃ t : invariantCoordinates ρ,
      v default ∈ B.toScheme.basicOpen t.val ∧
      ∀ {K' : Type} [Field K'] [IsAlgClosed K']
        (χ : invariantCoordinates ρ →+* K'), χ t ≠ 0 →
      ∃ w : Γ(B.toScheme, ⊤) →+* K',
        (∀ r : invariantCoordinates ρ, w r.val = χ r) ∧
        (lifted w) default ∈ completeInterior («p» := p) («q» := q) (Fin n) o' ∧
        Complete (Fin n) o' (lifted w) ∧
        ∀ w' : Γ(B.toScheme, ⊤) →+* K',
          (∀ r : invariantCoordinates ρ, w' r.val = χ r) →
          Complete (Fin n) o' (lifted w') ∧
          ∃! b : Spec (.of K') ⟶ (relation f hL d V c k).left,
            b ≫ p = (lifted w) ≫ normalizedFullRelationFirst f hL d V c k n o' ∧
            b ≫ q = (lifted w') ≫ normalizedFullRelationFirst f hL d V c k n o' := by
  have hv := (mixed_original_arrow_interior_iff e (Fin n) o o' u (v ≫ B.ι) a ha hb).mp hi
  obtain ⟨t, ht, hC⟩ := exists_complete_principal_character_neighborhood e (Fin n) o'
    B hB (v default) hv
  refine ⟨t, ht, ?_⟩
  intro K' _ _ χ hχ
  obtain ⟨w, hw, hiw, hcw, hall⟩ := hC χ hχ
  exact ⟨w, hw, hiw, hcw, fun w' hw' ↦ (hall w' hw').2⟩

end FLT.Mazur.HilbertChart.AffineRestriction
