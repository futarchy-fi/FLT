/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatSubschemeQuotient
public import FLT.Mazur.SmoothFiniteFlatIdealCharts

/-!
# Finite flat closed families in affine smooth curves are Cartier

For an affine smooth curve morphism over an arbitrary scheme, a finite flat
finitely presented closed family is a relative effective Cartier divisor.
The actual quotient maps, coefficient localizations, smooth coordinates,
ideal presentations, and scheme neighborhoods are all constructed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
  [SmoothOfRelativeDimension 1 f]

/-- Finite flat presented closed families in affine smooth relative curves are Cartier. -/
theorem effectiveCartier_of_affine_smooth_finite_flat (I : X.IdealSheafData)
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)] : EffectiveCartier I := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U, hU.preimage f⟩
  have hfp := finitePresentation_subscheme_ideal_quotient f I ⟨U, hU⟩ V.2
  have hflat := flat_subscheme_ideal_quotient f I ⟨U, hU⟩ V.2
  rw [f.app_eq_appLE] at hfp hflat
  obtain ⟨r, hr, hI⟩ := cartierChart_neighborhood_of_smooth_finite_flat
    f I ⟨U, hU⟩ V le_rfl hfp hflat x hx
  exact ⟨X.affineBasicOpen r, hr, hI⟩

/-- The Cartier condition and the family's given flatness assemble the relative divisor. -/
theorem relativeEffectiveCartier_of_affine_smooth_finite_flat (I : X.IdealSheafData)
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)] : RelativeEffectiveCartier f I :=
  ⟨effectiveCartier_of_affine_smooth_finite_flat f I, inferInstance⟩

/-- Finite locally free degree supplies all family hypotheses of the affine curve criterion. -/
theorem relativeEffectiveCartier_of_affine_smooth_degree (I : X.IdealSheafData) (d : ℕ)
    (h : FiniteLocallyFreeDegree (I.subschemeι ≫ f) d) : RelativeEffectiveCartier f I := by
  let _ := h.1
  let _ := h.2.1
  let _ := h.2.2.1
  exact relativeEffectiveCartier_of_affine_smooth_finite_flat f I

end FLT.Mazur.FCurve
