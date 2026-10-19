/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSpecializationOriginalScalarGeometry
public import FLT.Mazur.EquivalenceRelationCompleteScalarStrata
public import FLT.Mazur.EquivalenceRelationWholeScalarGeometry
public import FLT.Mazur.EquivalenceRelationScalarDefectCharacters
public import FLT.Mazur.HilbertSourceTestChartGenerators

/-!
# Complete image and whole-fiber scalar strata on fixed Hilbert charts

Finite scalar equations describe the exact complete image and, separately,
the exact locus with nonempty complete full fibers. All original chart data
remain fixed. No component interior anchors are required. Noetherianity of the
original scalar ring is still an explicit input for finite presentation.
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

/-- The unchanged invariant scalar map is finitely presented over Noetherian original scalars. -/
theorem normalizedChart_originalScalar_finitePresentation [IsNoetherianRing Ω] :
    (σ).FinitePresentation := by
  let _ := (σ).toAlgebra
  exact Algebra.FinitePresentation.of_finiteType.mp
    (originalSource_invariantScalar_finiteType f hL d V c k n o W B hB hBW)

/-- All scalar primes with a complete fixed-chart lift are covered, including image boundaries. -/
theorem exists_original_complete_image_strata [IsNoetherianRing Ω] :
    ∃ pieces : Finset (Ω × Finset Ω), ∀ P : PrimeSpectrum Ω,
      (∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ↔
      ∃ w : Γ(B.toScheme, ⊤) →+* K P,
        w.comp s = algebraMap Ω (K P) ∧ Complete (Fin n) o (u w) := by
  exact exists_complete_scalar_image_strata_of_finiteType e (Fin n) o B hB σ
    (normalizedChart_prescribedScalar_finiteType f hL d V c k W n o B hB hBW)

/-- Finite scalar equations also detect exactly the nonempty wholly complete original fibers. -/
theorem exists_original_wholeComplete_scalar_strata [IsNoetherianRing Ω] :
    ∃ pieces : Finset (Ω × Finset Ω), ∀ P : PrimeSpectrum Ω,
      P ∈ wholeCompleteScalarLocus e (Fin n) o B hB σ ↔
        ∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal := by
  let _ := originalSource_affine_isNoetherian f hL d V c k n o B
    (show IsAffine B.toScheme from inferInstance)
  exact exists_wholeCompleteScalarLocus_strata e (Fin n) o B hB σ
    (normalizedChart_originalScalar_finitePresentation f hL d V c k W n o B hB hBW)

/-- Each prime of the whole-complete locus has geometry over its own original residue closure. -/
theorem exists_original_wholeScalar_geometry (P : PrimeSpectrum Ω)
    (hP : P ∈ wholeCompleteScalarLocus e (Fin n) o B hB σ) :
    ∃ w : Γ(B.toScheme, ⊤) →+* K P,
      w.comp s = algebraMap Ω (K P) ∧ Complete (Fin n) o (u w) ∧
      sourceCharacterMap w ≫ scalarMorphism s =
        Spec.map (CommRingCat.ofHom (algebraMap Ω (K P))) := by
  exact exists_wholeScalar_residue_character e (Fin n) o B hB σ
    (normalizedChart_prescribedScalar_finiteType f hL d V c k W n o B hB hBW) P hP

/-- Every full character over a covered scalar prime retains its field and original arrows. -/
theorem exists_original_wholeScalar_full_character (P : PrimeSpectrum Ω)
    (hP : P ∈ wholeCompleteScalarLocus e (Fin n) o B hB σ)
    {F : Type} [Field F] [IsAlgClosed F] (χ : invariantCoordinates ρ →+* F)
    (hχ : PrimeSpectrum.comap σ (PrimeSpectrum.comap χ ⊥) = P) :
    ∃ w : Γ(B.toScheme, ⊤) →+* F,
      (∀ r : invariantCoordinates ρ, w r.val = χ r) ∧ Complete (Fin n) o (u w) ∧
      ∀ v : Γ(B.toScheme, ⊤) →+* F,
        (∀ r : invariantCoordinates ρ, v r.val = χ r) → Complete (Fin n) o (u v) ∧
        ∃! a : Spec (.of F) ⟶ (relation f hL d V c k).left,
          a ≫ p = (u w) ≫ normalizedFullRelationFirst f hL d V c k n o ∧
          a ≫ q = (u v) ≫ normalizedFullRelationFirst f hL d V c k n o := by
  exact exists_wholeScalar_full_character e (Fin n) o B hB σ P hP χ hχ

/-- Excluded primes in the actual original scalar image have concrete incomplete characters. -/
theorem exists_original_scalar_defect_character (P : PrimeSpectrum Ω)
    (hr : P ∈ Set.range (PrimeSpectrum.comap σ))
    (hP : P ∉ wholeCompleteScalarLocus e (Fin n) o B hB σ) :
    ∃ w : Γ(B.toScheme, ⊤) →+* K P,
      w.comp s = algebraMap Ω (K P) ∧ ¬ Complete (Fin n) o (u w) ∧
        ∃ t ∈ completeAffineOrbitIdeal e (Fin n) o B hB, w t.val ≠ 0 := by
  exact exists_incomplete_scalar_defect_character e (Fin n) o B hB σ
    (originalSource_invariantScalar_finiteType f hL d V c k n o W B hB hBW) P hr hP

end FLT.Mazur.HilbertChart.AffineRestriction
