/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenSubschemeQuotientProperties
public import FLT.Mazur.SmoothQuasiFiniteIdealCharts
public import FLT.Mazur.RelativeCartier

/-!
# The relative Cartier criterion with a presented full ideal

On an arbitrary smooth relative curve, a flat locally quasi-finite closed
family is Cartier if its ideal is finitely presented on affine opens.
The quotient hypotheses are derived from the actual family morphism;
no affine or support-containing ambient chart is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f]

/-- Presented ideals of flat quasi-finite closed families on smooth curves are Cartier. -/
theorem effectiveCartier_of_smooth_quasiFinite_flat_presented (I : X.IdealSheafData)
    [LocallyQuasiFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    (hfp : ∀ V : X.affineOpens, Module.FinitePresentation Γ(X, V) (I.ideal V)) :
    EffectiveCartier I := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  let _ := hfp ⟨V, hV⟩
  obtain ⟨r, hr, hI⟩ := cartierChart_neighborhood_of_smooth_quasiFinite_flat
    f I ⟨U, hU⟩ ⟨V, hV⟩ hVU
    (quasiFinite_open_subscheme_ideal_quotient f I ⟨U, hU⟩ ⟨V, hV⟩ hVU)
    (flat_open_subscheme_ideal_quotient f I ⟨U, hU⟩ ⟨V, hV⟩ hVU) x hxV
  exact ⟨X.affineBasicOpen r, hr, hI⟩

/-- The actual family's flatness completes the relative Cartier conclusion. -/
theorem relativeEffectiveCartier_of_smooth_quasiFinite_flat_presented
    (I : X.IdealSheafData) [LocallyQuasiFinite (I.subschemeι ≫ f)]
    [Flat (I.subschemeι ≫ f)]
    (hfp : ∀ V : X.affineOpens, Module.FinitePresentation Γ(X, V) (I.ideal V)) :
    RelativeEffectiveCartier f I :=
  ⟨effectiveCartier_of_smooth_quasiFinite_flat_presented f I hfp, inferInstance⟩

end FLT.Mazur.FCurve
