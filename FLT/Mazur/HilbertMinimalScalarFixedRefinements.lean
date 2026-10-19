/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRelatedFixedScalarCharts
public import FLT.Mazur.RelativeRelationMinimalScalarCharacters

/-!
# Minimal original scalar characters connect to independently fixed charts

The constructed W453 frame now controls every related fixed chart of the same
size, with any distinguished label. Refinement preserves the exact fixed test
map and the full original scalar character. Neither existence of an original
arrow from scalar equality nor arbitrary scalar-prime coverage is asserted.
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

/-- Construct one minimal scalar lift and refinements in all equally sized related fixed charts. -/
theorem exists_minimal_scalar_related_fixed_refinements (hW : IsAffineOpen E)
    (P : PrimeSpectrum Ω) (hP : P.asIdeal ∈ minimalPrimes Ω) :
    ∃ (n : ℕ) (o : Fin n)
      (u : Spec (.of (K P)) ⟶ normalizedFullRelationFrames f hL d V c k n o),
      Complete (Fin n) o u ∧
      ∀ (o' : Fin n) (B : (normalizedFullRelationFrames f hL d V c k n o').Opens)
        (_hB : ∀ g : Equiv.Perm (Fin n),
          (normalizedFullRelationAction f hL d V c k n o' g).hom ⁻¹ᵁ B = B)
        (hBW : B ≤ normalizedFullRelationFirst f hL d V c k n o' ⁻¹ᵁ E)
        (v : Spec (.of (K P)) ⟶ B.toScheme)
        (a : Spec (.of (K P)) ⟶ (relation f hL d V c k).left)
        (_ha : a ≫ p = u ≫ normalizedFullRelationFirst f hL d V c k n o)
        (_hb : a ≫ q = (v ≫ B.ι) ≫ normalizedFullRelationFirst f hL d V c k n o'),
      ∃ (U : (normalizedFullRelationFrames f hL d V c k n o').Opens)
        (hU : ∀ g : Equiv.Perm (Fin n),
          (normalizedFullRelationAction f hL d V c k n o' g).hom ⁻¹ᵁ U = U)
        (hUB : U ≤ B) (z : Spec (.of (K P)) ⟶ U.toScheme),
        IsAffineOpen U ∧ z ≫ U.ι = v ≫ B.ι ∧
        z ≫ scalarMorphism
          (invariantScalarCoordinates
            (restrictedAction (normalizedFullRelationAction f hL d V c k n o') U hU)
            (normalizedOriginalScalarMap f hL d V c k n o' W U hU (hUB.trans hBW))) =
          Spec.map (CommRingCat.ofHom (algebraMap Ω (K P))) ∧
        ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o' := by
  obtain ⟨b, n, o, u, hb, hu, hc, hi⟩ := exists_minimal_scalar_complete_frame eo W P e hW
    (originalOrbitSource_scalar_finiteType f hL d V c k W hW) hP
  refine ⟨n, o, u, hc, ?_⟩
  intro o' B hB hBW v a ha hb'
  exact exists_related_fixed_scalar_chart f hL d V c k W
    (algebraMap Ω (K P)) b hb n o o' u hu hi B hB hBW v a ha hb'

end FLT.Mazur.HilbertChart.AffineRestriction
