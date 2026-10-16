/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryBaseLocalizationMaps
public import FLT.Mazur.BoundaryCorrectionIdeal

/-!
# Computing the original lifting ideal by full mixed corrections

On the actual finite covering atlas, the original scalar lifting ideal equals
the ideal computed from exact chart boundary kernels and every full mixed
relation. The chosen chart lifts do not change this ideal. This is an equality
of ideals in the unchanged original invariant section ring.
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
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
/-- The packaged original scalar maps agree on every full mixed relation. -/
theorem originalChartScalarMap_full_compatible (j l : Charts)
    (a : (invariantSheaf e).obj.obj (op W)) : F j l (α j a) = G j l (α l a) := by
  simpa only [originalChartScalarMap_apply, MixedFrames.ChartFamily.firstCoefficientMap,
    MixedFrames.ChartFamily.secondCoefficientMap, RingHom.comp_apply, Subring.subtype_apply,
    CommRingCat.Hom.hom] using scalarFamily_compatible f hL d V c k W hW a j l

/-- The packaged scalar map retains the exact original boundary naturality equation. -/
theorem originalChartScalarMap_boundary (a : (invariantSheaf e).obj.obj (op W)) (j : Charts) :
    H j (α j a) = normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
      j.val.domain j.val.stable j.val.overDomain (originalClosedSectionPullback f hL d V c k W a) :=
  (congrArg (H j) (originalChartScalarMap_apply f hL d V c k W hW a j)).trans
    (scalarFamily_boundary f hL d V c k W hW a j)

/-- Original lifting ideal membership is equivalent to exact compatible chart numerators. -/
theorem original_liftIdeal_mem_iff_numerators (a : (invariantSheaf e).obj.obj (op W)) :
    a ∈ originalBoundaryLiftIdeal f hL d V c k W t ↔
      ∃ w : Sections f hL d V c k W hW,
        (∀ j : Charts, H j (w j) = H j (α j a) *
          normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
            j.val.domain j.val.stable j.val.overDomain t) ∧
        ∀ j l : Charts, F j l (w j) = G j l (w l) := by
  constructor
  · intro ha
    change ∃ b, originalClosedSectionPullback f hL d V c k W b =
      originalClosedSectionPullback f hL d V c k W a * t at ha
    obtain ⟨b, hb⟩ := ha
    refine ⟨fun j ↦ α j b, fun j ↦ ?_, ?_⟩
    · have hm := boundaryCoefficient_power_mul f hL d V c k W hW t
        (originalClosedSectionPullback f hL d V c k W a) 1 j
      simp only [pow_one] at hm
      exact (originalChartScalarMap_boundary f hL d V c k W hW b j).trans
        ((congrArg (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
          j.val.domain j.val.stable j.val.overDomain) hb).trans
          (hm.trans (congrArg (fun v ↦ v *
            normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
              j.val.domain j.val.stable j.val.overDomain t)
              (originalChartScalarMap_boundary f hL d V c k W hW a j).symm)))
    · exact originalChartScalarMap_full_compatible f hL d V c k W hW
        (a := b)
  · rintro ⟨w, hb, hc⟩
    have h := original_power_mem_of_scaled_boundary f hL d V c k W hW t a 1 w
      (fun j ↦ by simpa only [pow_one, ← originalChartScalarMap_apply] using hb j) hc
    simpa only [pow_one] using h

/-- The full simultaneous correction ideal computed on the actual finite original atlas. -/
def originalCorrectionIdeal : Ideal ((invariantSheaf e).obj.obj (op W)) :=
  BoundaryCorrectionIdeal.ideal α H F G
    (originalChartScalarMap_full_compatible f hL d V c k W hW)
    (lifts f hL d V c k W hW t)

attribute [local irreducible] originalCorrectionIdeal

/-- The computed correction ideal is exactly the original boundary lifting ideal. -/
theorem originalCorrectionIdeal_eq_liftIdeal :
    originalCorrectionIdeal f hL d V c k W hW t =
      originalBoundaryLiftIdeal f hL d V c k W t := by
  apply Ideal.ext
  intro a
  unfold originalCorrectionIdeal
  have h := BoundaryCorrectionIdeal.mem_iff_numerators α H F G
    (originalChartScalarMap_full_compatible f hL d V c k W hW)
    (lifts f hL d V c k W hW t) a
  simp only [lifts_restrict] at h
  exact h.trans (original_liftIdeal_mem_iff_numerators f hL d V c k W hW t a).symm

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
