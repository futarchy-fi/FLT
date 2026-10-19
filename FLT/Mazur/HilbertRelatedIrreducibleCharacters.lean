/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRelatedPrincipalCharacters
public import FLT.Mazur.EquivalenceRelationIrreducibleCompleteCharacters

/-!
# All characters on related fixed irreducible Hilbert charts

An actual original arrow transfers a complete interior point to an independently
fixed affine chart of the same size with preirreducible full quotient. Closedness then covers its
entire full invariant spectrum, without shrinking to a principal neighborhood.
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
  [PreirreducibleSpace (quotient (restrictedAction
    (normalizedFullRelationAction f hL d V c k n o') B hB))]
local notation "ρ" => restrictedAction (normalizedFullRelationAction f hL d V c k n o') B hB
local notation "lifted" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
attribute [local irreducible] invariantSheaf normalizedOriginalScalarMap
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete scalarMorphism
  EquivalenceRelationNormalizedFrames.action restrictedAction invariantScalarCoordinates
  sourceCharacterMap

/-- A related fixed irreducible chart has complete geometry for every full character. -/
theorem exists_related_irreducible_character {K : Type} [Field K]
    (u : Spec (.of K) ⟶ normalizedFullRelationFrames f hL d V c k n o)
    (hi : u default ∈ completeInterior («p» := p) («q» := q) (Fin n) o)
    (v : Spec (.of K) ⟶ B.toScheme) (a : Spec (.of K) ⟶ (relation f hL d V c k).left)
    (ha : a ≫ p = u ≫ normalizedFullRelationFirst f hL d V c k n o)
    (hb : a ≫ q = (v ≫ B.ι) ≫ normalizedFullRelationFirst f hL d V c k n o')
    {F : Type} [Field F] [IsAlgClosed F] (χ : invariantCoordinates ρ →+* F) :
    ∃ w : Γ(B.toScheme, ⊤) →+* F,
      (∀ r : invariantCoordinates ρ, w r.val = χ r) ∧ Complete (Fin n) o' (lifted w) ∧
      ∀ w' : Γ(B.toScheme, ⊤) →+* F,
        (∀ r : invariantCoordinates ρ, w' r.val = χ r) →
        Complete (Fin n) o' (lifted w') ∧
        ∃! b : Spec (.of F) ⟶ (relation f hL d V c k).left,
          b ≫ p = (lifted w) ≫ normalizedFullRelationFirst f hL d V c k n o' ∧
          b ≫ q = (lifted w') ≫ normalizedFullRelationFirst f hL d V c k n o' := by
  have hv := (mixed_original_arrow_interior_iff e (Fin n) o o' u (v ≫ B.ι) a ha hb).mp hi
  let _ : PreirreducibleSpace (quotient (restrictedAction (action e (Fin n) o') B hB)) :=
    inferInstanceAs (PreirreducibleSpace (quotient ρ))
  exact exists_complete_irreducible_character e (Fin n) o' B hB (v default) hv χ

end FLT.Mazur.HilbertChart.AffineRestriction
