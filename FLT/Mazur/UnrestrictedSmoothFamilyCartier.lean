/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleQuasiFiniteCartierDescent
public import FLT.Mazur.OpenSubschemeQuotientProperties
public import FLT.Mazur.FiniteLocallyFreeDegreeAffine

/-!
# The unrestricted relative Cartier criterion for smooth curves

A flat, locally quasi-finite, finitely presented closed family in any smooth
relative curve is relative effective Cartier. Standard-smooth coordinates,
etale finite branches, and fppf neighborhood descent construct the equations.
Neither a Noetherian base, an affine ambient morphism, nor a finite
presentation of the ideal is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}

/-- The ideal in affine coordinates sheafifies to the actual pullback along the affine chart. -/
theorem baseIdeal_affineChart_eq_comap (I : X.IdealSheafData) (V : X.affineOpens) :
    BaseAdicThickening.baseIdeal Γ(X, V) (I.ideal V) = I.comap V.2.fromSpec := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  let h : (⊤ : (Spec Γ(X, V)).Opens) ≤ V.2.fromSpec ⁻¹ᵁ V.1 := by
    rw [V.2.fromSpec_preimage_self]
  have he : V.2.fromSpec.appLE V.1 ⊤ h = (Scheme.ΓSpecIso Γ(X, V)).inv := by
    rw [Scheme.Hom.appLE, V.2.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    have hh : (eqToHom V.2.fromSpec_preimage_self).op ≫ (homOfLE h).op = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [hh, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [BaseAdicThickening.baseIdeal_top, Scheme.IdealSheafData.ideal_comap I V.2.fromSpec V
    ⟨⊤, isAffineOpen_top _⟩ h, he]

variable (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f]

/-- Every flat presented quasi-finite closed family on a smooth relative curve is Cartier. -/
theorem effectiveCartier_of_smooth_quasiFinite_flat (I : X.IdealSheafData)
    [LocallyQuasiFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)] : EffectiveCartier I := by
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  let _ := (f.appLE U V e).hom.toAlgebra
  let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Y, U) Γ(X, V) := hg
  let _ := flat_open_subscheme_ideal_quotient f I ⟨U, hU⟩ ⟨V, hV⟩ e
  let _ := quasiFinite_open_subscheme_ideal_quotient f I ⟨U, hU⟩ ⟨V, hV⟩ e
  let _ := finitePresentation_open_subscheme_ideal_quotient f I ⟨U, hU⟩ ⟨V, hV⟩ e
  have hI : EffectiveCartier (I.comap hV.fromSpec) := by
    rw [← baseIdeal_affineChart_eq_comap I ⟨V, hV⟩]
    exact effectiveCartier_baseIdeal_of_smooth_quasiFinite_flat (R := Γ(Y, U)) (I.ideal ⟨V, hV⟩)
  obtain ⟨W, hxW, hW⟩ := hI (hV.primeIdealOf ⟨x, hxV⟩)
  refine ⟨⟨hV.fromSpec ''ᵁ W, W.2.image_of_isOpenImmersion hV.fromSpec⟩,
    ⟨hV.primeIdealOf ⟨x, hxV⟩, hxW, hV.fromSpec_primeIdealOf ⟨x, hxV⟩⟩, ?_⟩
  exact (cartierChart_comap_iff I hV.fromSpec W).mp hW

/-- Actual family flatness completes the unrestricted relative Cartier criterion. -/
theorem relativeEffectiveCartier_of_smooth_quasiFinite_flat (I : X.IdealSheafData)
    [LocallyQuasiFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)] : RelativeEffectiveCartier f I :=
  ⟨effectiveCartier_of_smooth_quasiFinite_flat f I, inferInstance⟩

/-- Every finite locally free closed family in a smooth relative curve is relative Cartier. -/
theorem relativeEffectiveCartier_of_smooth_degree (I : X.IdealSheafData) (d : ℕ)
    (h : FiniteLocallyFreeDegree (I.subschemeι ≫ f) d) : RelativeEffectiveCartier f I := by
  let _ := h.1
  let _ := h.2.1
  let _ := h.2.2.1
  exact relativeEffectiveCartier_of_smooth_quasiFinite_flat f I

end FLT.Mazur.FCurve
