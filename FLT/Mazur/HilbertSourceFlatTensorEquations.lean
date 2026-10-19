/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceTestKernelObstruction
public import FLT.Mazur.AffineBoundaryFlatTensorEquations
public import FLT.Mazur.SchemeFiniteGroupQuotientFiniteType

/-!
# Arbitrary flat scalar algebras for original Hilbert rank tests

Exact equations on the full boundary coordinate tensor product exclude
higher original rank. The scalar algebra need not be finitely presented;
faithful flatness supplies its own point above an original scalar prime.
The equations at required residual primes remain geometric obligations.
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
local instance tensorEquationChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance tensorEquationOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance tensorEquationOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance tensorEquationProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW
local notation "higher" => boundaryRankOpen n o U e hU σ κ (n + 1)
local notation "φ" => boundaryHigherScalarMap n o U e hU σ κ

/-- Full tensor equations on any flat scalar algebra recover the unchanged frame size n. -/
theorem originalSource_ceiling_eq_of_flat_tensor_equations
    (S : Type) [CommRing S] [Algebra Tsource S] [Module.Flat Tsource S]
    (Q : PrimeSpectrum S)
    (h : ∀ t ∈ tests, ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧
      boundaryTensorPowerEquation σ κ S t x k) :
    ceiling (PrimeSpectrum.comap (algebraMap Tsource S) Q) = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ _).mp
  exact boundaryScalar_mem_of_flat_tensor_equations σ κ S tests Q h

/-- The same algebraic equations produce an entire original matching-rank neighborhood. -/
theorem originalSource_rank_chart_of_flat_tensor_equations
    (S : Type) [CommRing S] [Algebra Tsource S] [Module.Flat Tsource S]
    (Q : PrimeSpectrum S)
    (h : ∀ t ∈ tests, ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧
      boundaryTensorPowerEquation σ κ S t x k) :
    ∃ t : Tsource, t ∉ Q.asIdeal.comap (algebraMap Tsource S) ∧ ∃ stage : ℕ,
      IsIso (rankPullbackMap (Over.mk p)
        (boundaryPrincipalEndpoint n o U e hU σ κ (boundaryScalarHom σ κ t)) n stage) := by
  apply originalSource_scalar_rank_chart f hL d V c k n o W U hU hUW
    (PrimeSpectrum.comap (algebraMap Tsource S) Q)
  exact boundaryScalar_mem_of_flat_tensor_equations σ κ S tests Q h

/-- An arbitrary faithfully flat scalar algebra supplies actual points above the original prime. -/
theorem originalSource_ceiling_eq_of_faithfully_flat_tensor
    (S : Type) [CommRing S] [Algebra Tsource S] [Module.FaithfullyFlat Tsource S]
    (P : PrimeSpectrum Tsource)
    (h : ∀ Q : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap Tsource S) Q = P →
      ∀ t ∈ tests, ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧
        boundaryTensorPowerEquation σ κ S t x k) : ceiling P = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp
  exact boundaryScalar_mem_of_faithfully_flat_tensor σ κ S tests P h

/-- Different tests can use independent flat scalar algebras, preserving the original prime. -/
theorem originalSource_ceiling_eq_of_independent_flat_tensor
    (Ss : tests → Type) [∀ t, CommRing (Ss t)] [∀ t, Algebra Tsource (Ss t)]
    [∀ t, Module.Flat Tsource (Ss t)] (P : PrimeSpectrum Tsource)
    (Qs : ∀ t, PrimeSpectrum (Ss t))
    (hQ : ∀ t, PrimeSpectrum.comap (algebraMap Tsource (Ss t)) (Qs t) = P)
    (h : ∀ t, ∃ (x : Ss t) (k : ℕ), x ∉ (Qs t).asIdeal ∧
      boundaryTensorPowerEquation σ κ (Ss t) t.val x k) : ceiling P = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp
  exact boundaryScalar_mem_of_independent_flat_tensor σ κ tests Ss P Qs hQ h

end FLT.Mazur.HilbertChart.AffineRestriction
