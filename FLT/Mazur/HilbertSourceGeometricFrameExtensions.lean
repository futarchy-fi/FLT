/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceGeometricFiberTests
public import FLT.Mazur.EquivalenceRelationGeometricTestExtensions

/-!
# Original Hilbert residual witnesses as strict normalized frame extensions

A failed exact matching fiber now supplies an actual larger normalized frame
at the original source endpoint over the canonical residue closure. All old
arrows, the original scalar triangle, and the first endpoint are retained.
Original arrows from complete frames independently prove zero test values.
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
local instance geometricFrameExtensionChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance geometricFrameExtensionOver_etale : Etale (Over.mk p).hom :=
  inferInstanceAs (Etale p)
local instance geometricFrameExtensionOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance geometricFrameExtensionProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW
local notation "higher" => boundaryRankOpen n o U e hU σ κ (n + 1)
local notation "φ" => boundaryHigherScalarMap n o U e hU σ κ


open ScalarTestLocalization
attribute [local irreducible] boundaryPointRank boundaryScalarProjection

local notation "K" P => AlgebraicClosure (PrimeSpectrum.comap κ P).asIdeal.ResidueField
local notation "u" w => sourceCharacterMap w ≫ U.ι

/-- An actual original arrow from a complete frame proves the fixed source test values. -/
theorem originalSource_character_tests_of_complete_arrow (P : PrimeSpectrum Tsource)
    (w : Γ(U.toScheme, ⊤) →+* K P)
    (v : Spec (.of (K P)) ⟶ N) (hv : Complete (Fin n) o v)
    (a : Spec (.of (K P)) ⟶ (relation f hL d V c k).left)
    (ha : a ≫ p = v ≫ first p q (Fin n) o)
    (hb : a ≫ q = (u w) ≫ first p q (Fin n) o) :
    ∀ t ∈ tests, w t.val = 0 :=
  original_arrow_character_tests_vanish e (Fin n) o U hU w v hv a ha hb

/-- A failed exact fiber gives a scalar-compatible character in no complete-frame orbit. -/
theorem originalSource_matching_failure_no_complete_arrow (P : PrimeSpectrum Tsource)
    (pointZ : boundaryProduct σ κ) (hz : boundaryScalarProjection σ κ pointZ = P)
    (hn : rankOf pointZ ≠ n) :
    ∃ w : Γ(U.toScheme, ⊤) →+* K P,
      w.comp σ₀ = algebraMap Ω (K P) ∧
      ∀ v : Spec (.of (K P)) ⟶ N, Complete (Fin n) o v →
        ¬ ∃ a : Spec (.of (K P)) ⟶ (relation f hL d V c k).left,
          a ≫ p = v ≫ first p q (Fin n) o ∧ a ≫ q = (u w) ≫ first p q (Fin n) o := by
  have hbad : ¬ ∀ w : Γ(U.toScheme, ⊤) →+* K P,
      w.comp σ₀ = algebraMap Ω (K P) → ∃ v : Spec (.of (K P)) ⟶ N,
        Complete (Fin n) o v ∧ ∃ a : Spec (.of (K P)) ⟶ (relation f hL d V c k).left,
          a ≫ p = v ≫ first p q (Fin n) o ∧ a ≫ q = (u w) ≫ first p q (Fin n) o := by
    intro h
    apply hn
    apply originalSource_matching_of_source_point_values f hL d V c k n o W U hU hUW P
      (fun w hw ↦ ?_) pointZ hz
    obtain ⟨v, hv, a, ha, hb⟩ := h w hw
    exact original_arrow_character_tests_vanish e (Fin n) o U hU w v hv a ha hb
  push Not at hbad
  simpa only [not_exists, not_and] using hbad

/-- Failed exact matching constructs an extra original arrow, preserving the entire old frame. -/
theorem originalSource_matching_failure_strict_extension (P : PrimeSpectrum Tsource)
    (pointZ : boundaryProduct σ κ) (hz : boundaryScalarProjection σ κ pointZ = P)
    (hn : rankOf pointZ ≠ n) :
    ∃ w : Γ(U.toScheme, ⊤) →+* K P,
      w.comp σ₀ = algebraMap Ω (K P) ∧
      ∃ v : Spec (.of (K P)) ⟶ source p q (Option (Fin n)) (some o),
        v ≫ first p q (Option (Fin n)) (some o) = (u w) ≫ first p q (Fin n) o ∧
        (∀ idx, v ≫ coordinate p q (Option (Fin n)) (some o) (some idx) =
          (u w) ≫ coordinate p q (Fin n) o idx) ∧
        ∀ idx, v ≫ coordinate p q (Option (Fin n)) (some o) none ≠
          (u w) ≫ coordinate p q (Fin n) o idx := by
  have hbad : ¬ ∀ w : Γ(U.toScheme, ⊤) →+* K P,
      w.comp σ₀ = algebraMap Ω (K P) → Complete (Fin n) o (u w) := by
    intro h
    apply hn
    apply originalSource_matching_of_source_point_values f hL d V c k n o W U hU hUW P
      (fun w hw ↦ ?_) pointZ hz
    exact complete_character_tests_vanish e (Fin n) o U hU w (h w hw)
  push Not at hbad
  obtain ⟨w, hw, hnc⟩ := hbad
  exact ⟨w, hw, exists_strict_normalized_extension (Fin n) o (u w) hnc⟩

end FLT.Mazur.HilbertChart.AffineRestriction
