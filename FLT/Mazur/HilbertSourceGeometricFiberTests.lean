/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceIntegralFlatTests
public import FLT.Mazur.AffineBoundaryGeometricFiberTests
public import FLT.Mazur.InvariantGeometricFiberTests

/-!
# Original Hilbert matching fibers from geometric source points

Construct matching exact original fibers from values on original coordinate
points in a fixed residue closure. Integral full flat test charts then give
the original rank ceiling, preserving n. The source point vanishing and
branch integrality remain geometric obligations.
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
local instance geometricSourceTestChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance geometricSourceTestOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance geometricSourceTestOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance geometricSourceTestProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW
local notation "higher" => boundaryRankOpen n o U e hU σ κ (n + 1)
local notation "φ" => boundaryHigherScalarMap n o U e hU σ κ


open ScalarTestLocalization

/-- The exact original matching fiber is detected in one canonical residue closure. -/
theorem originalSource_matching_iff_residue_tests (P : PrimeSpectrum Tsource) :
    (∀ pointZ : boundaryProduct σ κ, boundaryScalarProjection σ κ pointZ = P →
      rankOf pointZ = n) ↔
      ∀ t ∈ tests, residueGeometricTest σ (PrimeSpectrum.comap κ P) t := by
  rw [← boundary_exact_fiber_iff_residue_tests σ κ
    (originalSource_invariantScalar_finiteType f hL d V c k n o W U hU hUW) tests P]
  constructor
  · exact originalSource_matching_fiber_tests f hL d V c k n o W U hU hUW P
  · intro h pointZ hz
    apply (boundaryTestIdeal_le_iff_matching_rank n o U e hU σ κ pointZ).mp
    exact (boundaryTestIdeal_le_point_iff σ κ tests pointZ).mpr (h pointZ hz)

local notation "K" P => AlgebraicClosure (PrimeSpectrum.comap κ P).asIdeal.ResidueField

/-- Original coordinate-valued points construct the entire exact original matching fiber. -/
theorem originalSource_matching_of_source_point_values (P : PrimeSpectrum Tsource)
    (hg : ∀ w : Γ(U.toScheme, ⊤) →+* K P,
      w.comp σ₀ = algebraMap Ω (K P) → ∀ t ∈ tests, w t.val = 0) :
    ∀ pointZ : boundaryProduct σ κ, boundaryScalarProjection σ κ pointZ = P →
      rankOf pointZ = n := by
  apply (originalSource_matching_iff_residue_tests f hL d V c k n o W U hU hUW P).mpr
  let _ := SchemeCoordinateAction.coordinateAction τU
  intro t ht
  apply (FiniteGroupQuotient.residueGeometricTest_iff_source_values
    (Equiv.Perm (Fin n)) Γ(U.toScheme, ⊤) σ (PrimeSpectrum.comap κ P) t).mpr
  intro w hw
  apply hg w _ t ht
  convert hw using 1
  congr 1
  unfold invariantScalarCoordinates
  rfl

/-- Source geometric values and full integral branches give the unchanged original ceiling. -/
theorem originalSource_ceiling_eq_of_source_geometric_integral_tests
    (S : Type) [CommRing S] [Algebra Tsource S] [Module.Flat Tsource S]
    (Q : PrimeSpectrum S)
    (hi : ∀ t ∈ tests, boundaryIntegralFlatTest σ κ S Q t)
    (hg : ∀ w : Γ(U.toScheme, ⊤) →+* K (PrimeSpectrum.comap (algebraMap Tsource S) Q),
      w.comp σ₀ = algebraMap Ω _ → ∀ t ∈ tests, w t.val = 0) :
    ceiling (PrimeSpectrum.comap (algebraMap Tsource S) Q) = n := by
  apply originalSource_ceiling_eq_of_integral_flat_tests
    f hL d V c k n o W U hU hUW S Q hi
  exact originalSource_matching_of_source_point_values f hL d V c k n o W U hU hUW _ hg

/-- A mismatching exact fiber constructs an original source point with a nonzero fixed test. -/
theorem originalSource_matching_failure_geometric_point (P : PrimeSpectrum Tsource)
    (pointZ : boundaryProduct σ κ) (hz : boundaryScalarProjection σ κ pointZ = P)
    (hn : rankOf pointZ ≠ n) :
    ∃ t ∈ tests, ∃ w : Γ(U.toScheme, ⊤) →+* K P,
      w.comp σ₀ = algebraMap Ω (K P) ∧ w t.val ≠ 0 := by
  have hbad : ¬ ∀ w : Γ(U.toScheme, ⊤) →+* K P,
      w.comp σ₀ = algebraMap Ω (K P) → ∀ t ∈ tests, w t.val = 0 := by
    intro h
    exact hn (originalSource_matching_of_source_point_values
      f hL d V c k n o W U hU hUW P h pointZ hz)
  push Not at hbad
  obtain ⟨w, hw, t, ht, hnt⟩ := hbad
  exact ⟨t, ht, w, hw, hnt⟩

end FLT.Mazur.HilbertChart.AffineRestriction
