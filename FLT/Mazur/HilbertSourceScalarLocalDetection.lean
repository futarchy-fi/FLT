/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceScalarResidualStages
public import FLT.Mazur.EquivalenceRelationScalarLocalDetection

/-!
# Original Hilbert coefficient detection on Noetherian scalar-local tests

The original Hilbert hypotheses give the Noetherian rank base and the finite
flat faithful chart. All computed bounded stages detect sections on every
locally Noetherian test of the unchanged scalar local product. The product
itself is not assumed Noetherian, and original source lift existence is open.
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


variable [IsAffine U.toScheme]
local instance scalarDetectionChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance scalarDetectionOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance scalarDetectionOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance scalarDetectionProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW
local notation "localProduct" => boundaryScalarLocalProduct σ κ

/-- All original bounded stage orders detect each full Noetherian scalar-local test. -/
theorem originalSource_scalarLocal_test_zero (P : PrimeSpectrum Tsource)
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] (v : Y ⟶ localProduct P)
    (a : Γ(localProduct P, ⊤))
    (ha : ∀ rankM : ℕ, n ≤ rankM → rankM ≤ ceiling P → ∀ powK : ℕ,
      (boundaryScalarLocalRankMap n o U e hU σ κ P rankM powK).appTop a = 0) :
    v.appTop a = 0 := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact boundaryScalarLocal_test_zero n o U e hU σ κ P v a ha

/-- Equality of the original coefficients is retained on every such test with its nilpotents. -/
theorem originalSource_scalarLocal_test_eq (P : PrimeSpectrum Tsource)
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] (v : Y ⟶ localProduct P)
    (a a' : Γ(localProduct P, ⊤))
    (ha : ∀ rankM : ℕ, n ≤ rankM → rankM ≤ ceiling P → ∀ powK : ℕ,
      (boundaryScalarLocalRankMap n o U e hU σ κ P rankM powK).appTop a =
        (boundaryScalarLocalRankMap n o U e hU σ κ P rankM powK).appTop a') :
    v.appTop a = v.appTop a' := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact boundaryScalarLocal_test_eq n o U e hU σ κ P v a a' ha

/-- Any nonzero Noetherian test is witnessed at a bounded finite original rank order. -/
theorem originalSource_scalarLocal_nonzero_stage (P : PrimeSpectrum Tsource)
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] (v : Y ⟶ localProduct P)
    (a : Γ(localProduct P, ⊤)) (ha : v.appTop a ≠ 0) :
    ∃ rankM : ℕ, n ≤ rankM ∧ rankM ≤ ceiling P ∧ ∃ powK : ℕ,
      (boundaryScalarLocalRankMap n o U e hU σ κ P rankM powK).appTop a ≠ 0 := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact boundaryScalarLocal_nonzero_stage n o U e hU σ κ P v a ha

/-- Full coefficient detection follows if the actual scalar-local product is locally Noetherian. -/
theorem originalSource_scalarLocal_section_zero (P : PrimeSpectrum Tsource)
    [IsLocallyNoetherian (localProduct P)] (a : Γ(localProduct P, ⊤))
    (ha : ∀ rankM : ℕ, n ≤ rankM → rankM ≤ ceiling P → ∀ powK : ℕ,
      (boundaryScalarLocalRankMap n o U e hU σ κ P rankM powK).appTop a = 0) : a = 0 := by
  simpa using originalSource_scalarLocal_test_zero f hL d V c k n o W U hU hUW P
    (𝟙 (localProduct P)) a ha

end FLT.Mazur.HilbertChart.AffineRestriction
