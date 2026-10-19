/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRelatedPrincipalCharacters
public import FLT.Mazur.SchemeInvariantPrincipalScalarImage

/-!
# Complete lifts over the prescribed scalar image of a principal neighborhood

The fixed chart supplies finite type over the original scalars. An interior
complete point then constructs one invariant principal open whose entire
original scalar image has complete lifts over each scalar prime's canonical
residue closure. The original scalar ring, frame size and label are retained.
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

/-- The fixed affine chart is finite type over the unchanged prescribed scalar ring. -/
theorem normalizedChart_prescribedScalar_finiteType : (s).FiniteType := by
  let _ : LocallyOfFiniteType A.hom := by
    rw [← k.w]
    infer_instance
  let _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let g := B.ι ≫ normalizedFullRelationFirst f hL d V c k n o ≫
    A.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
  let _ : LocallyOfFiniteType g := by dsimp only [g]; infer_instance
  let _ := integerCoordinates_finiteType g
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℤ Ω)
  have he : (s).comp (algebraMap ℤ Ω) = algebraMap ℤ Γ(B.toScheme, ⊤) :=
    Subsingleton.elim _ _
  rw [he]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

attribute [local irreducible] scalarResidueClosureField scalarResidueClosureAlgebra

/-- Every scalar prime in the constructed principal image has an exact complete lift. -/
theorem exists_principal_original_scalar_geometry (x : B.toScheme)
    (hx : B.ι x ∈ completeInterior («p» := p) («q» := q) (Fin n) o) :
    ∃ t : invariantCoordinates ρ,
      x ∈ B.toScheme.basicOpen t.val ∧
      scalarMorphism s x ∈ PrimeSpectrum.comap σ '' (PrimeSpectrum.basicOpen t : Set _) ∧
      ∀ P : PrimeSpectrum Ω,
        P ∈ PrimeSpectrum.comap σ '' (PrimeSpectrum.basicOpen t : Set _) →
      ∃ w : Γ(B.toScheme, ⊤) →+* K P,
        sourceCharacterMap w default ∈ B.toScheme.basicOpen t.val ∧
        (u w) default ∈ completeInterior («p» := p) («q» := q) (Fin n) o ∧
        Complete (Fin n) o (u w) ∧
        sourceCharacterMap w ≫ scalarMorphism s =
          Spec.map (CommRingCat.ofHom (algebraMap Ω (K P))) := by
  obtain ⟨t, ht, hC⟩ := exists_complete_invariant_principal e (Fin n) o B hB x hx
  have hp : scalarMorphism s x ∈
      PrimeSpectrum.comap σ '' (PrimeSpectrum.basicOpen t : Set _) := by
    rw [← invariant_principal_scalar_image ρ σ t]
    exact ⟨x, ht, rfl⟩
  refine ⟨t, ht, hp, fun P hP ↦ ?_⟩
  obtain ⟨w, hw, hi⟩ := exists_scalar_character_of_invariant_principal ρ σ t
    (normalizedChart_prescribedScalar_finiteType f hL d V c k W n o B hB hBW) P hP
  have hc : (u w) default ∈ completeInterior («p» := p) («q» := q) (Fin n) o := hC _ hi
  refine ⟨w, hi, hc, (complete_iff_mem_completePointLocus (Fin n) o (u w)).mpr
    (completeInterior_subset (Fin n) o hc), ?_⟩
  rw [sourceCharacterMap_scalar, hw]

end FLT.Mazur.HilbertChart.AffineRestriction
