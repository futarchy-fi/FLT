/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryBaseCorrectionCriterion
public import FLT.Mazur.HilbertOrbitBoundaryCorrectionIdeal
public import FLT.Mazur.RelativeRelationPointDenominators

/-!
# Exact point-localized solvability locus on the original Hilbert quotient

Compatible solutions in the actual base-localized chart rings exist exactly
when the original lifting ideal meets the chosen multiplicative set. At an
orbit point this gives exactly the original principal lifting locus. No
identification of a localization with a sheaf stalk is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source
namespace OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] finiteCharts lifts obstruction
  scalarFamily normalizedBoundaryChartMap normalizedOrbitBoundaryCoefficient
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

open BaseLocalizationMap
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "n" => fun j : Charts ↦ j.val.size
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "F" => MixedFrames.ChartFamily.firstCoefficientMap ef n o U hU
local notation "G" => MixedFrames.ChartFamily.secondCoefficientMap ef n o U hU
local notation "H" => fun j : Charts ↦ normalizedBoundaryChartMap f hL d V c k j.val.size
  j.val.label j.val.domain j.val.stable

attribute [local irreducible] originalChartScalarMap
local notation "α" => originalChartScalarMap f hL d V c k W hW
variable (M : Submonoid ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
/-- The original lifting ideal detects solvability in the specified chart localizations. -/
theorem original_base_localized_iff_liftIdeal_meets :
    (∃ v : ∀ j : Charts, baseLocalizedChartRing f hL d V c k W hW M j,
      (∀ j : Charts, baseLocalizedBoundaryMap f hL d V c k W hW M j (v j) =
        algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label
          W j.val.domain j.val.stable j.val.overDomain t)) ∧
      (∀ j l : Charts, baseLocalizedFirstMap f hL d V c k W hW M j l (v j) =
        baseLocalizedSecondMap f hL d V c k W hW M j l (v l))) ↔
      ∃ s : M, s.val ∈ originalBoundaryLiftIdeal f hL d V c k W t := by
  rw [original_base_localized_iff_scaled_correction]
  apply exists_congr
  intro s
  exact Iff.of_eq (congrArg (fun I : Ideal ((invariantSheaf e).obj.obj (op W)) ↦ s.val ∈ I)
    (originalCorrectionIdeal_eq_liftIdeal f hL d V c k W hW t))

variable (x : Orbit (equivalence f hL d V c k)) (hx : x ∈ W)

omit [IsAffine V.left] in
/-- Point denominators meet the original lifting ideal precisely on its actual lifting open. -/
theorem original_pointDenominators_meet_iff :
    (∃ s : pointDenominators e W x hx,
      s.val ∈ originalBoundaryLiftIdeal f hL d V c k W t) ↔
      x ∈ originalBoundaryLiftOpen f hL d V c k W t := by
  change (∃ s : pointDenominators e W x hx,
    s.val ∈ originalBoundaryLiftIdeal f hL d V c k W t) ↔
      x ∈ sectionIdealOpen (ringedSpace e) W
        (originalBoundaryLiftIdeal f hL d V c k W t)
  rw [mem_sectionIdealOpen]
  exact ⟨fun ⟨s, hs⟩ ↦ ⟨s.val, hs, s.property⟩, fun ⟨s, hs, hx⟩ ↦ ⟨⟨s, hx⟩, hs⟩⟩

/-- Actual point-localized full compatibility exists exactly on the original lifting locus. -/
theorem original_point_localized_iff_mem_liftOpen :
    (∃ v : ∀ j : Charts,
      baseLocalizedChartRing f hL d V c k W hW (pointDenominators e W x hx) j,
      (∀ j : Charts, baseLocalizedBoundaryMap f hL d V c k W hW
        (pointDenominators e W x hx) j (v j) =
          algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label
            W j.val.domain j.val.stable j.val.overDomain t)) ∧
      (∀ j l : Charts, baseLocalizedFirstMap f hL d V c k W hW
        (pointDenominators e W x hx) j l (v j) =
          baseLocalizedSecondMap f hL d V c k W hW (pointDenominators e W x hx) j l (v l))) ↔
      x ∈ originalBoundaryLiftOpen f hL d V c k W t :=
  (original_base_localized_iff_liftIdeal_meets f hL d V c k W hW
    (pointDenominators e W x hx) t).trans
    (original_pointDenominators_meet_iff f hL d V c k W t x hx)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
