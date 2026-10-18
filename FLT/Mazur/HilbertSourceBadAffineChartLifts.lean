/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceConstructedBadAffineCover
public import FLT.Mazur.HilbertSourceConstructedOpenPrimeTests
public import FLT.Mazur.SchemeBadAffineCoverLocalIntegral

/-!
# Full original Hilbert lifts from the constructed affine bad charts

Local integrality is required only on the actual finite bad atlas. A complete
original scalar fiber then gives exact full-compatible numerators and source
surjectivity. Neither ambient relation affineness nor a closed scalar image
is assumed, and no independent target chart is substituted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
local notation "hr" => originalClosedFst_isPullback f hL d V c k
local notation "hs" => congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)
local notation "E" => (pullOpen eo W).val

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS
local notation "τU" => restrictedAction τ U hU
local notation "jU" => j ∣_ U
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σ₀" => invariantScalarCoordinates τU σ
local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

attribute [local irreducible] normalizedOriginalScalarMap
  SchemeRelationRestriction.doubleDomain SchemeRelationRestriction.fst
  SchemeRelationRestriction.snd SchemeRelationRestriction.arrow

local notation "Bsource" => invariantCoordinates (boundaryOpenAction ρ τ j hj U hU)
local notation "α" => normalizedOriginalBoundaryHom f hL d V c k n o W U hU hUW

attribute [local irreducible] normalizedOriginalBoundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction
  normalizedFullRelationAction
  originalSourceCompatibleModule

local notation "Csource" => originalSourceCompatibleModule f hL d V c k n o W U hU hUW
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

attribute [local irreducible] OriginalPrimeIntegralFiber.localizedMap
  invariantSheaf sourceSheaf invariantInclusion originalClosedSectionPullback
  invariantScalarCoordinates

open SchemeScalarPrincipalNeighborhood
local notation "Lgood" => originalSourceGoodRelationOpen f hL d V c k n o U hU
local notation "Ogood" => originalSourceConstructedOpen f hL d V c k n o U hU
local notation "σR" => (F).appTop.hom.comp σ₀


open SchemeBadAffineCover
variable [IsAffine U.toScheme]
attribute [local instance] originalBadAtlasNoetherian
local notation "BC" => badCover Lgood
/-- Construct one exact kernel separator for each actual affine bad chart. -/
theorem originalSource_exists_badChart_kernel_separators (P : Ideal Tsource) [P.IsPrime]
  (hInt : ∀ idx : (BC).I₀,
    (OriginalPrimeIntegralFiber.localizedMap
      (badChartScalar σR Lgood idx) (P.comap κ)).IsIntegral)
  (hP : ∀ x : U.toScheme, scalarMorphism σ₀ x = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
    U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    ∃ a : (BC).I₀ → Ω,
      ∀ idx, κ (a idx) ∉ P ∧ badChartScalar σR Lgood idx (a idx) = 0 :=
  exists_badChart_kernel_separators σR Lgood (PrimeSpectrum.comap κ ⟨P, inferInstance⟩)
    hInt (originalSourceGoodRelationOpen_scalar_fiber f hL d V c k n o W U hU hUW P hP)

/-- Local integrality on the actual bad charts proves original-prime safety. -/
theorem originalSource_safe_of_badChart_local_integral (P : Ideal Tsource) [P.IsPrime]
  (hInt : ∀ idx : (BC).I₀,
    (OriginalPrimeIntegralFiber.localizedMap
      (badChartScalar σR Lgood idx) (P.comap κ)).IsIntegral)
  (hP : ∀ x : U.toScheme, scalarMorphism σ₀ x = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
    U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈ scalarNeighborhoodLocus σR Lgood :=
  (mem_scalarNeighborhoodLocus_iff_badChart_local_integral σR Lgood
    (PrimeSpectrum.comap κ ⟨P, inferInstance⟩) hInt).mpr
      (originalSourceGoodRelationOpen_scalar_fiber f hL d V c k n o W U hU hUW P hP)

/-- The constructed safe denominator yields full-compatible numerators, including nilpotents. -/
theorem originalSource_numerator_of_badChart_local_integral (P : Ideal Tsource) [P.IsPrime]
  (hInt : ∀ idx : (BC).I₀,
    (OriginalPrimeIntegralFiber.localizedMap
      (badChartScalar σR Lgood idx) (P.comap κ)).IsIntegral)
  (hP : ∀ x : U.toScheme, scalarMorphism σ₀ x = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
    U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) (t : Bsource) :
    ∃ x₀ : Ω, κ x₀ ∉ P ∧ ∃ w : Sinv,
      normalizedBoundaryChartMap f hL d V c k n o U hU w =
        normalizedBoundaryChartMap f hL d V c k n o U hU (σ x₀) * t ∧
      w.val ∈ SchemeEffectiveEpiSections.compatibleFunctions F H :=
  originalSource_constructedOpen_boundary_numerator f hL d V c k n o W U hU hUW
    (show IsAffine U.toScheme from inferInstance) P
    (originalSource_safe_of_badChart_local_integral f hL d V c k n o W U hU hUW P hInt hP) t

/-- The same constructed bad-chart separators give full original localized source surjectivity. -/
theorem originalSource_surjective_of_badChart_local_integral (P : Ideal Tsource) [P.IsPrime]
  (hInt : ∀ idx : (BC).I₀,
    (OriginalPrimeIntegralFiber.localizedMap
      (badChartScalar σR Lgood idx) (P.comap κ)).IsIntegral)
  (hP : ∀ x : U.toScheme, scalarMorphism σ₀ x = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
    U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) :=
  originalSource_constructedOpen_surjective f hL d V c k n o W U hU hUW
    (show IsAffine U.toScheme from inferInstance) P
    (originalSource_safe_of_badChart_local_integral f hL d V c k n o W U hU hUW P hInt hP)

end FLT.Mazur.HilbertChart.AffineRestriction
