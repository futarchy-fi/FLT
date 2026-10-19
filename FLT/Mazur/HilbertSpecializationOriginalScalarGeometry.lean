/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPrincipalOriginalScalarGeometry
public import FLT.Mazur.EquivalenceRelationSpecializationScalarGeometry

/-!
# Fixed-chart geometry over original scalar images of invariant specializations

A complete point in a fixed chart controls all invariant primes specializing
its quotient point, and all original scalar primes in their image. The frame
size, distinguished label and original orbit domain stay fixed.
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

/-- Original scalar specialization-image coverage on the unchanged fixed Hilbert chart. -/
theorem exists_original_scalar_specialization_geometry (x : B.toScheme)
    (hx : B.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (P : PrimeSpectrum Ω)
    (hP : ∃ Q : PrimeSpectrum (invariantCoordinates ρ),
      (quotientMap ρ x).asIdeal ≤ Q.asIdeal ∧ PrimeSpectrum.comap σ Q = P) :
    ∃ w : Γ(B.toScheme, ⊤) →+* K P,
      w.comp s = algebraMap Ω (K P) ∧ Complete (Fin n) o (u w) ∧
      (quotientMap ρ x).asIdeal ≤ (quotientMap ρ (sourceCharacterMap w default)).asIdeal ∧
      sourceCharacterMap w ≫ scalarMorphism s =
        Spec.map (CommRingCat.ofHom (algebraMap Ω (K P))) := by
  exact exists_complete_specialization_scalar_character e (Fin n) o B hB σ
    (normalizedChart_prescribedScalar_finiteType f hL d V c k W n o B hB hBW) x hx P hP

/-- Every specialized full invariant prime also keeps its exact full residue character. -/
theorem exists_fixed_complete_full_specialization (x : B.toScheme)
    (hx : B.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (Q : PrimeSpectrum (invariantCoordinates ρ))
    (hQ : (quotientMap ρ x).asIdeal ≤ Q.asIdeal) :
    ∃ w : Γ(B.toScheme, ⊤) →+* scalarResidueClosure Q,
      (∀ r : invariantCoordinates ρ,
        w r.val = algebraMap (invariantCoordinates ρ) (scalarResidueClosure Q) r) ∧
      Complete (Fin n) o (u w) := by
  exact exists_complete_specialization_character e (Fin n) o B hB x hx Q hQ

end FLT.Mazur.HilbertChart.AffineRestriction
