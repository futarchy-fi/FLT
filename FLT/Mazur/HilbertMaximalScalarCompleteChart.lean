/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOriginalScalarStrata
public import FLT.Mazur.HilbertOriginalScalarFrameCharts
public import FLT.Mazur.EquivalenceRelationScalarFrameRanks

/-!
# Maximal original scalar frame charts have whole complete fibers

The maximum ranges over actual frames above the fixed original scalar
character. A defect in any maximal-size affine chart would construct a larger
frame with the very same scalar map, contradicting that maximum.
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

local notation "s₀" => orbitScalarCoordinates eo W
local notation "t" P => Spec.map (CommRingCat.ofHom (algebraMap Ω (K P)))
local notation "j" => (normalizedFullRelationFirst f hL d V c k n o).resLE E B hBW

/-- A maximal-size actual scalar chart has nonempty and entirely complete full fibers. -/
theorem original_wholeScalar_of_maximal_frameSize (P : PrimeSpectrum Ω)
    (hmax : ∀ m ∈ scalarFrameSizes («p» := p) («q» := q) E s₀ (t P), m ≤ n)
    (hr : P ∈ Set.range (PrimeSpectrum.comap σ)) :
    P ∈ wholeCompleteScalarLocus e (Fin n) o B hB σ := by
  by_contra hP
  obtain ⟨w, hw, hn, _⟩ :=
    exists_original_scalar_defect_character f hL d V c k W n o B hB hBW P hr hP
  let b := sourceCharacterMap w ≫ j
  have hu : (u w) ≫ normalizedFullRelationFirst f hL d V c k n o = b ≫ (E).ι := by
    simp only [b, Category.assoc, Scheme.Hom.resLE_comp_ι]
  have hb : b ≫ scalarMorphism s₀ = t P := by
    change sourceCharacterMap w ≫ j ≫ scalarMorphism s₀ = _
    rw [← normalizedSource_scalarMorphism_factor f hL d V c k W n o B hB hBW,
      sourceCharacterMap_scalar, hw]
  exact hn (complete_of_maximal_scalarFrameSize e E s₀ (t P) n hmax o (u w) b hu hb)

end FLT.Mazur.HilbertChart.AffineRestriction
