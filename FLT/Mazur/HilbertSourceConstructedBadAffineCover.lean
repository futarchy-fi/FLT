/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceConstructedFiniteBadPrimes
public import FLT.Mazur.SchemeBadAffineCoverFiniteType

/-!
# Actual finite affine bad charts over the original Hilbert scalars

The full relation is Noetherian and locally of finite type over the integers.
Its constructed bad atlas therefore has finite original scalar generators.
All bad-chart points retain their original incomplete first endpoints.
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

local instance originalBadAtlasNoetherian : IsNoetherian D :=
  originalSource_doubleRelation_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

local notation "BC" => badCover Lgood

omit [IsAffine U.toScheme] in
/-- The actual full double relation is locally of finite type over the integers. -/
theorem originalSource_doubleRelation_integer_finiteType :
    LocallyOfFiniteType (F ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o ≫
      A.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) := by
  let _ : LocallyOfFiniteType A.hom := by
    rw [← k.w]
    infer_instance
  let _ := SchemeRelationRestriction.fst_locallyOfFiniteType p q kS
  let _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  infer_instance

/-- Every actual affine bad chart point has an incomplete original first endpoint. -/
theorem originalSource_badChart_first_incomplete (idx : (BC).I₀) (x : (BC).X idx) :
    (F ≫ U.ι) (badChartMap Lgood idx x) ∉
      completePointLocus («p» := p) («q» := q) (Fin n) o :=
  originalSource_badRelation_first_incomplete f hL d V c k n o U hU _
    (badChartMap_not_mem Lgood idx x)

/-- Original invariant scalars generate each constructed affine bad chart up to finite type. -/
theorem originalSource_badChartScalar_finiteType (idx : (BC).I₀) :
    (badChartScalar σR Lgood idx).FiniteType := by
  let g := F ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o ≫
    A.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
  let _ := originalSource_doubleRelation_integer_finiteType f hL d V c k n o U
  exact badChartScalar_finiteType σR Lgood g idx

/-- Finite original scalar generators are constructed, rather than assumed on the bad charts. -/
theorem originalSource_exists_badChart_finite_generators (idx : (BC).I₀) :
    ∃ a : Finset Γ((BC).X idx, ⊤),
      Subring.closure (Set.range (badChartScalar σR Lgood idx) ∪ (a : Set _)) = ⊤ := by
  let g := F ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o ≫
    A.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
  let _ := originalSource_doubleRelation_integer_finiteType f hL d V c k n o U
  exact exists_badChart_finite_generators σR Lgood g idx

end FLT.Mazur.HilbertChart.AffineRestriction
