/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPrescribedScalarMorphism
public import FLT.Mazur.RelativeRelationMinimalScalarCharacters

/-!
# Geometric complete-chart lifts of prescribed minimal scalar primes

Every minimal prime of the unchanged original scalar ring has a complete
affine stable chart and a point over its canonical residue closure. Equality
of the scalar scheme maps retains the entire scalar character. The chart size
is constructed; arbitrary prescribed sizes and nonminimal primes remain separate.
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

/-- A full original scalar character lifts to a constructed complete affine chart. -/
theorem exists_original_minimal_scalar_geometric_chart (hW : IsAffineOpen E)
    (P : PrimeSpectrum Ω) (hP : P.asIdeal ∈ minimalPrimes Ω) :
    ∃ (n : ℕ) (o : Fin n)
      (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hU : ∀ g : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
      (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E)
      (z : Spec (.of (K P)) ⟶ U.toScheme),
      IsAffineOpen U ∧
      z ≫ scalarMorphism
        (invariantScalarCoordinates
          (restrictedAction (normalizedFullRelationAction f hL d V c k n o) U hU)
          (normalizedOriginalScalarMap f hL d V c k n o W U hU hUW)) =
        Spec.map (CommRingCat.ofHom (algebraMap Ω (K P))) ∧
      Complete (Fin n) o (z ≫ U.ι) ∧
      ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o := by
  obtain ⟨b, n, o, u, hb, hu, hc, hi⟩ := exists_minimal_scalar_complete_frame eo W P e hW
    (originalOrbitSource_scalar_finiteType f hL d V c k W hW) hP
  have hx : normalizedFullRelationFirst f hL d V c k n o (u default) ∈ E := by
    change (u ≫ first p q (Fin n) o) default ∈ E
    rw [hu]
    exact (b default).property
  obtain ⟨U, hU, hUW, ha, hxU, hC, _⟩ :=
    exists_completeInterior_orbit_chart f hL d V c k W n o (u default) hx hi
  have hr : Set.range u ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y default]
    exact hxU
  let z := IsOpenImmersion.lift U.ι u hr
  have hz : z ≫ U.ι = u := IsOpenImmersion.lift_fac _ _ _
  have he : z ≫ (normalizedFullRelationFirst f hL d V c k n o).resLE E U hUW = b := by
    apply (cancel_mono (E).ι).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hz]
    exact hu
  refine ⟨n, o, U, hU, hUW, z, ha, ?_, ?_, hC⟩
  · rw [normalizedSource_scalarMorphism_factor, ← Category.assoc, he]
    exact hb
  · rwa [hz]

end FLT.Mazur.HilbertChart.AffineRestriction
