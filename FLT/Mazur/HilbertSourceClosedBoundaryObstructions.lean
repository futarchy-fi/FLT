/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceConstructedBadAffineCover
public import FLT.Mazur.HilbertSourceConstructedOpenPrimeTests
public import FLT.Mazur.SchemeBadAffineCoverBoundaryBaseChange
public import FLT.Mazur.SchemeBadAffineCoverBoundaryWitness
public import FLT.Mazur.SchemeBadAffineCoverGeometricBoundaryTests

/-!
# Closed obstructions on the unchanged original Hilbert boundary

The bad affine atlas constructs a finite family of explicit quotient schemes
on the original boundary spectrum. Their emptiness is exactly universal source
prime avoidance and supplies full source lifts. Every nonempty obstruction has
an actual incomplete first-endpoint witness over an original generization.
No unconditional emptiness or independent-target extension is asserted.
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
/-- The actual closed obstruction for one original Hilbert bad chart. -/
def originalSourceBoundaryObstruction (idx : (BC).I₀) : Scheme :=
  boundaryChartObstruction σR Lgood κ idx

/-- Each constructed obstruction retains its original boundary scalar prime. -/
def originalSourceBoundaryObstructionMap (idx : (BC).I₀) :
    originalSourceBoundaryObstruction f hL d V c k n o W U hU hUW idx ⟶
      Spec (.of Tsource) :=
  boundaryChartObstructionι σR Lgood κ idx

local notation "Zbad" => originalSourceBoundaryObstruction f hL d V c k n o W U hU hUW
local notation "zbad" => originalSourceBoundaryObstructionMap f hL d V c k n o W U hU hUW

/-- The original universal prime test is exactly emptiness of the actual closed obstructions. -/
theorem originalSource_all_safe_iff_closed_obstructions_empty :
    (∀ P : PrimeSpectrum Tsource,
      PrimeSpectrum.comap κ P ∈ scalarNeighborhoodLocus σR Lgood) ↔
      ∀ idx : (BC).I₀, IsEmpty (Zbad idx) :=
  all_scalar_safe_iff_boundaryChart_empty σR Lgood κ

/-- Empty closed obstructions construct a finite original boundary denominator equation. -/
theorem originalSource_equation_of_closed_obstructions_empty
    (h : ∀ idx : (BC).I₀, IsEmpty (Zbad idx)) :
    ∃ (m' : ℕ) (a : Fin m' → Ω) (weights : Fin m' → Tsource),
      (∀ idx, (D).basicOpen (σR (a idx)) ≤ Lgood) ∧
        ∑ idx, weights idx * κ (a idx) = 1 := by
  apply (scalar_boundary_unit_ideal_iff_finite_equation σR Lgood κ).mp
  apply (scalar_boundary_cover_iff_unit_ideal σR Lgood κ).mp
  exact (originalSource_all_safe_iff_closed_obstructions_empty
    f hL d V c k n o W U hU hUW).mpr h

/-- Empty obstructions give full source lifts at each original boundary prime. -/
theorem originalSource_surjective_of_closed_obstructions_empty
    (h : ∀ idx : (BC).I₀, IsEmpty (Zbad idx)) (P : Ideal Tsource) [P.IsPrime] :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) :=
  originalSource_constructedOpen_surjective f hL d V c k n o W U hU hUW
    (show IsAffine U.toScheme from inferInstance) P
    ((originalSource_all_safe_iff_closed_obstructions_empty
      f hL d V c k n o W U hU hUW).mpr h ⟨P, inferInstance⟩)

/-- A point of the obstruction produces an incomplete original endpoint over a generization. -/
theorem originalSource_closed_obstruction_incomplete_witness (idx : (BC).I₀)
    (x : Zbad idx) :
    ∃ y : U.toScheme,
      U.ι y ∉ completePointLocus («p» := p) («q» := q) (Fin n) o ∧
        (scalarMorphism σ₀ y).asIdeal ≤ (zbad idx x).asIdeal.comap κ := by
  obtain ⟨y, hy, hP⟩ := boundaryChart_point_has_ambient_witness σR Lgood κ idx x
  refine ⟨F y, originalSource_badRelation_first_incomplete f hL d V c k n o U hU y hy, ?_⟩
  rw [scalarMorphism_comp] at hP
  exact hP

/-- Faithfully flat tests return a denominator equation over the original boundary section ring. -/
theorem originalSource_equation_of_closed_obstructions_faithfullyFlat
    (S : Type) [CommRing S] [Algebra Tsource S] [Module.FaithfullyFlat Tsource S]
    (h : ∀ idx : (BC).I₀,
      IsEmpty (boundaryChartObstruction σR Lgood ((algebraMap Tsource S).comp κ) idx)) :
    ∃ (m' : ℕ) (a : Fin m' → Ω) (weights : Fin m' → Tsource),
      (∀ idx, (D).basicOpen (σR (a idx)) ≤ Lgood) ∧
        ∑ idx, weights idx * κ (a idx) = 1 :=
  boundary_equation_of_faithfullyFlat σR Lgood κ h

/-- All geometric boundary scalar values detect exactly the original closed obstructions. -/
theorem originalSource_closed_obstructions_empty_iff_geometric :
    (∀ idx : (BC).I₀, IsEmpty (Zbad idx)) ↔
      ∀ (idx : (BC).I₀) (K : Type) [Field K] [IsAlgClosed K] (φ : Tsource →+* K),
        ∃ a : Ω, badChartScalar σR Lgood idx a = 0 ∧ φ (κ a) ≠ 0 :=
  forall_congr' fun idx ↦ boundaryChart_empty_iff_geometric_separators σR Lgood κ idx

/-- Geometric boundary separation constructs full denominators over the unchanged original ring. -/
theorem originalSource_equation_of_geometric_boundary_separators
    (h : ∀ (idx : (BC).I₀) (K : Type) [Field K] [IsAlgClosed K] (φ : Tsource →+* K),
      ∃ a : Ω, badChartScalar σR Lgood idx a = 0 ∧ φ (κ a) ≠ 0) :
    ∃ (m' : ℕ) (a : Fin m' → Ω) (weights : Fin m' → Tsource),
      (∀ idx, (D).basicOpen (σR (a idx)) ≤ Lgood) ∧
        ∑ idx, weights idx * κ (a idx) = 1 :=
  boundary_equation_of_geometric_separators σR Lgood κ h

end FLT.Mazur.HilbertChart.AffineRestriction
