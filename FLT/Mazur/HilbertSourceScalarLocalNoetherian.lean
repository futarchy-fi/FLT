/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceScalarLocalDetection
public import FLT.Mazur.AffineBoundaryScalarLocalNoetherian
public import FLT.Mazur.HilbertRequiredScalarFiniteCover

/-!
# Noetherianity and exact detection on the original scalar-local product

The original boundary source supplies Noetherian stalks. The actual chart is
finite type over the unchanged invariant scalars, so its full local boundary
product is Noetherian. Bounded original rank stages therefore detect its
sections directly, with no extra Noetherianity hypothesis on that product.
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
local instance scalarLocalNoetherianChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance scalarLocalNoetherianOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance scalarLocalNoetherianOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance scalarLocalNoetherianProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW
local notation "localProduct" => boundaryScalarLocalProduct σ κ

/-- The actual full scalar-local product is Noetherian over the original boundary stalk. -/
theorem originalSource_scalarLocal_noetherian
    (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
    (P : PrimeSpectrum Tsource) : IsNoetherian (localProduct P) := by
  let _ := originalAmbientBoundary_noetherian f hL d V c k W hW
  exact boundaryScalarLocalProduct_noetherian σ κ
    (originalSource_invariantScalar_finiteType f hL d V c k n o W U hU hUW) P

/-- The actual unreduced scalar-local coordinate ring is Noetherian. -/
theorem originalSource_scalarLocal_coordinates_noetherian
    (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
    (P : PrimeSpectrum Tsource) : IsNoetherianRing Γ(localProduct P, ⊤) := by
  let _ := originalSource_scalarLocal_noetherian f hL d V c k n o W U hU hUW hW P
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- Original bounded rank tests detect the full local section without an added hypothesis. -/
theorem originalSource_scalarLocal_zero_of_stages
    (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
    (P : PrimeSpectrum Tsource) (a : Γ(localProduct P, ⊤))
    (ha : ∀ rankM : ℕ, n ≤ rankM → rankM ≤ ceiling P → ∀ powK : ℕ,
      (boundaryScalarLocalRankMap n o U e hU σ κ P rankM powK).appTop a = 0) : a = 0 := by
  let _ := originalSource_scalarLocal_noetherian f hL d V c k n o W U hU hUW hW P
  exact originalSource_scalarLocal_section_zero f hL d V c k n o W U hU hUW P a ha

/-- Equality is detected at the same original bounded ranks and every finite order. -/
theorem originalSource_scalarLocal_eq_of_stages
    (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
    (P : PrimeSpectrum Tsource) (a a' : Γ(localProduct P, ⊤))
    (hab : ∀ rankM : ℕ, n ≤ rankM → rankM ≤ ceiling P → ∀ powK : ℕ,
      (boundaryScalarLocalRankMap n o U e hU σ κ P rankM powK).appTop a =
        (boundaryScalarLocalRankMap n o U e hU σ κ P rankM powK).appTop a') : a = a' := by
  let _ := originalSource_scalarLocal_noetherian f hL d V c k n o W U hU hUW hW P
  simpa using originalSource_scalarLocal_test_eq f hL d V c k n o W U hU hUW P
    (𝟙 (localProduct P)) a a' hab

end FLT.Mazur.HilbertChart.AffineRestriction
