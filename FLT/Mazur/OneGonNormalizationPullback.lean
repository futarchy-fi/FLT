/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAffineNormalization
/-!
# Inverse images of the one-gon normalization charts

The inverse image of the pinched affine chart is the affine normalization
chart alpha, while the entire multiplicative chart pulls back identically.
These are cartesian squares for the already constructed normalization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
universe u
namespace FLT.Mazur.OneGonNormalizationPullback
open OneGonAffineNormalization OneGonNormalization PinchingAffineDescent
open PolygonNodePresentation OneGonTransition OneGonAffineCover
variable (K : Type u) [Field K]

/-- The entire multiplicative chart in the projective normalization. -/
abbrev torusLift := ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K

/-- The glued affine and torus charts meet exactly on their specified puncture. -/
theorem intersection (x : OneGonGluing.nodeChart K) (y : OneGonGluing.torusChart K)
    (h : OneGonGluing.node K x = OneGonGluing.torus K y) :
    ∃ z, bPuncture K z = x ∧ toTorus K z = y := by
  obtain ⟨i, fi, fj, z, hx, hy⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff
    (span (bPuncture K) (toTorus K))).mp h
  cases i with
  | none => cases fi; cases fj; exact ⟨z, hx, hy⟩
  | some i => cases i with
    | left => cases fj
    | right => cases fi

/-- The inverse image of the pinched chart is precisely alpha. -/
theorem preimage_node :
    normalization K ⁻¹ᵁ (OneGonGluing.node K).opensRange = (alpha K).opensRange := by
  ext x
  change normalization K x ∈ Set.range (OneGonGluing.node K) ↔ x ∈ Set.range (alpha K)
  constructor
  · rintro ⟨y, hy⟩
    rcases covers K x with hx | ⟨t, rfl⟩
    · exact hx
    · have ht : OneGonGluing.node K y = OneGonGluing.torus K t := by
        exact hy.trans (congrArg (fun f ↦ f t) (torus_normalization K))
      obtain ⟨z, _, hz⟩ := intersection K y t ht
      refine ⟨punctureOpen K z, ?_⟩
      change (punctureOpen K ≫ alpha K) z = _
      rw [puncture_alpha]
      change torusLift K (toTorus K z) = torusLift K t
      rw [hz]
  · rintro ⟨z, rfl⟩
    refine ⟨oneBranch K z, ?_⟩
    exact (congrArg (fun f ↦ f z) (alpha_normalization K)).symm

/-- The affine one-gon normalization is the restriction of the global map. -/
theorem node_isPullback :
    IsPullback (oneBranch K) (alpha K) (OneGonGluing.node K) (normalization K) :=
  IsOpenImmersion.isPullback _ _ _ _ (alpha_normalization K) (preimage_node K)

/-- The normalization is unchanged over the whole multiplicative chart. -/
theorem preimage_torus :
    normalization K ⁻¹ᵁ (OneGonGluing.torus K).opensRange = (torusLift K).opensRange := by
  ext x
  change normalization K x ∈ Set.range (OneGonGluing.torus K) ↔
    x ∈ Set.range (torusLift K)
  constructor
  · rintro ⟨t, ht⟩
    rcases covers K x with ⟨a, rfl⟩ | hx
    · have he : OneGonGluing.node K (oneBranch K a) = OneGonGluing.torus K t :=
        (congrArg (fun f ↦ f a) (alpha_normalization K)).symm.trans ht.symm
      obtain ⟨z, hz, _⟩ := intersection K _ _ he
      have ha : a ∈ Set.range (punctureOpen K) := by
        rw [show Set.range (punctureOpen K) =
          (PrimeSpectrum.basicOpen (X * (X - 1) : K[X]) : Set (PrimeSpectrum K[X])) from
          PrimeSpectrum.localization_away_comap_range _ _]
        have hb : oneBranch K a ∈ Set.range (bPuncture K) := ⟨z, hz⟩
        rw [range_bPuncture] at hb
        exact hb
      obtain ⟨s, rfl⟩ := ha
      refine ⟨toTorus K s, ?_⟩
      exact (congrArg (fun f ↦ f s) (puncture_alpha K)).symm
    · exact hx
  · rintro ⟨z, rfl⟩
    exact ⟨z, (congrArg (fun f ↦ f z) (torus_normalization K)).symm⟩

/-- The multiplicative chart pulls back to itself along normalization. -/
theorem torus_isPullback :
    IsPullback (𝟙 (OneGonGluing.torusChart K)) (torusLift K)
      (OneGonGluing.torus K) (normalization K) := by
  apply IsOpenImmersion.isPullback _ _ _ _ _ (preimage_torus K)
  simp [torusLift]
end FLT.Mazur.OneGonNormalizationPullback
