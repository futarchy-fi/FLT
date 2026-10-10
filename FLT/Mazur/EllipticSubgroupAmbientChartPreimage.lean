/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupAmbientMorphism
public import FLT.Mazur.WeierstrassCoefficientChartPreimage

/-!
# The closure charts are actual inverse images of the cubic charts

The kernel quotient carries each homogeneous coordinate to the corresponding
closure coordinate. Its nonvanishing opens therefore agree with the specified
gluing overlaps, so the ambient morphism has the expected cartesian charts.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- The closure overlap is exactly the corresponding homogeneous nonvanishing open. -/
theorem closureToLeft_range : Set.range (closureToLeft A W H j k) =
    (PrimeSpectrum.basicOpen (closureCoord A W H j k) : Set (PrimeSpectrum (Closure A W H j))) :=
  PrimeSpectrum.localization_away_comap_range _ _

/-- The opposite overlap inclusion has the range of the opposite principal open. -/
theorem closureToRight_range : Set.range (closureToRight A W H j k) =
    Set.range (closureToLeft A W H k j) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(closureIntersectionIso A W H j k).hom z, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := (closureIntersectionIso A W H j k).hom.surjective z
    exact ⟨y, rfl⟩

/-- Ambient membership in the other chart is exactly membership in the closure overlap. -/
theorem closureAmbientChart_mem_other (x : closureChart A W H j) :
    (closureAmbientChart A W H j ≫ integralCurveChart W j) x ∈
      Set.range (integralCurveChart W k) ↔ x ∈ Set.range (closureToLeft A W H j k) := by
  rw [closureToLeft_range]
  change closureAmbientChart A W H j x ∈
    integralCurveChart W j ⁻¹ᵁ (integralCurveChart W k).opensRange ↔ _
  rw [integralCurveChart_preimage_chart]
  rfl

/-- The first closure chart is the actual inverse image of the first cubic chart. -/
theorem closureToCurve_preimage_left :
    closureToCurve A W H j k ⁻¹ᵁ (integralCurveChart W j).opensRange =
      (closureLeft A W H j k).opensRange := by
  ext x
  change closureToCurve A W H j k x ∈ Set.range (integralCurveChart W j) ↔
    x ∈ Set.range (closureLeft A W H j k)
  constructor
  · intro hx
    rcases closure_charts_cover A W H j k x with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact ⟨q, rfl⟩
    · change (closureRight A W H j k ≫ closureToCurve A W H j k) q ∈ _ at hx
      rw [closureRight_toCurve] at hx
      have hq := (closureAmbientChart_mem_other A W H k j q).mp hx
      rw [← closureToRight_range A W H j k] at hq
      obtain ⟨z, rfl⟩ := hq
      exact ⟨closureToLeft A W H j k z,
        congrArg (fun f => f z) (closure_overlap_condition A W H j k)⟩
  · rintro ⟨q, rfl⟩
    exact ⟨closureAmbientChart A W H j q,
      (congrArg (fun f => f q) (closureLeft_toCurve A W H j k)).symm⟩

/-- The second closure chart is the actual inverse image of the second cubic chart. -/
theorem closureToCurve_preimage_right :
    closureToCurve A W H j k ⁻¹ᵁ (integralCurveChart W k).opensRange =
      (closureRight A W H j k).opensRange := by
  ext x
  change closureToCurve A W H j k x ∈ Set.range (integralCurveChart W k) ↔
    x ∈ Set.range (closureRight A W H j k)
  constructor
  · intro hx
    rcases closure_charts_cover A W H j k x with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · change (closureLeft A W H j k ≫ closureToCurve A W H j k) q ∈ _ at hx
      rw [closureLeft_toCurve] at hx
      obtain ⟨z, rfl⟩ := (closureAmbientChart_mem_other A W H j k q).mp hx
      exact ⟨closureToRight A W H j k z,
        (congrArg (fun f => f z) (closure_overlap_condition A W H j k)).symm⟩
    · exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨closureAmbientChart A W H k q,
      (congrArg (fun f => f q) (closureRight_toCurve A W H j k)).symm⟩

/-- The first chart square is cartesian as a square of schemes. -/
theorem closureAmbientChart_left_isPullback : IsPullback (closureAmbientChart A W H j)
    (closureLeft A W H j k) (integralCurveChart W j) (closureToCurve A W H j k) :=
  IsOpenImmersion.isPullback _ _ _ _ (closureLeft_toCurve A W H j k)
    (closureToCurve_preimage_left A W H j k)

/-- The second chart square is cartesian as a square of schemes. -/
theorem closureAmbientChart_right_isPullback : IsPullback (closureAmbientChart A W H k)
    (closureRight A W H j k) (integralCurveChart W k) (closureToCurve A W H j k) :=
  IsOpenImmersion.isPullback _ _ _ _ (closureRight_toCurve A W H j k)
    (closureToCurve_preimage_right A W H j k)

end FLT.Mazur.EllipticSubgroupChart
