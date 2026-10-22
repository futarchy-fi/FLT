/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNilpotentNormalForm
public import FLT.Mazur.OneGonSmoothingFamily
public import FLT.Mazur.WeierstrassVariableChangeZero
public import FLT.Mazur.WeierstrassVariableChangeSmoothIso

/-!
# The whole pointed cubic of an arbitrary nilpotent nodal deformation

The normalizing admissible change gives an isomorphism of the original proper
cubics over the original base and fixes their infinity sections. Its restriction
identifies the entire relative smooth loci, including the singular fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
open WeierstrassIntegralChart OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]

/-- Every element of a nilpotent ideal is nilpotent. -/
theorem nilpotent_of_mem (I : Ideal R) (hI : IsNilpotent I) {t : R} (ht : t ∈ I) :
    IsNilpotent t := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  have h := Ideal.pow_mem_pow ht n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

/-- Every infinitesimal parameter lies in the original arithmetic open. -/
theorem parameter_factor_unit (I : Ideal R) (hI : IsNilpotent I) {t : R} (ht : t ∈ I) :
    IsUnit (1 + 432 * t) :=
  (nilpotent_of_mem I hI (I.mul_mem_left 432 ht)).isUnit_one_add

/-- The original reduced nodal equation has an admissible presentation over the original ring. -/
theorem exists_relative_presentation (W : WeierstrassCurve R) (I : Ideal R)
    (hI : IsNilpotent I) (hW : W.map (Ideal.Quotient.mk I) = equation 0) :
    ∃ (C : VariableChange R) (t : R), C • W = equation t ∧
      C.map (Ideal.Quotient.mk I) = 1 ∧ t ∈ I ∧ IsUnit (1 + 432 * t) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := coefficients_mem_of_map_eq W I 0 hW
  have h₆ : W.a₆ ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp
    (congrArg WeierstrassCurve.a₆ hW)
  obtain ⟨C, t, he, hc, ht⟩ := nilpotent_normalForm_parameter W I hI h₁ h₂ h₃ h₄ h₆
  exact ⟨C, t, he, hc, ht, parameter_factor_unit I hI ht⟩

/-- Arbitrary nodal Weierstrass deformations have whole pointed one-gon presentations. -/
theorem exists_pointed_presentation (W : WeierstrassCurve R) (I : Ideal R)
    (hI : IsNilpotent I) (hW : W.map (Ideal.Quotient.mk I) = equation 0) :
    ∃ (t : R), t ∈ I ∧ IsUnit (1 + 432 * t) ∧
      ∃ e : family t ≅ Over.mk (integralCurveStructure W),
        marking t ≫ e.hom.left = integralCurveZero W := by
  obtain ⟨C, t, he, _, ht, hu⟩ := exists_relative_presentation W I hI hW
  exact ⟨t, ht, hu, integralVariableChangeOverIso W (equation t) C he,
    integralVariableChangeIso_zero W (equation t) C he⟩

/-- The same original cubic comparison identifies the entire smooth opens. -/
theorem exists_smooth_presentation (W : WeierstrassCurve R) (I : Ideal R)
    (hI : IsNilpotent I) (hW : W.map (Ideal.Quotient.mk I) = equation 0) :
    ∃ (t : R), t ∈ I ∧ IsUnit (1 + 432 * t) ∧
      ∃ (e : family t ≅ Over.mk (integralCurveStructure W))
        (g : Over.mk (integralSmoothStructure (equation t)) ≅
          Over.mk (integralSmoothStructure W)),
        g.hom.left ≫ (integralSmoothOpen W).ι =
          (integralSmoothOpen (equation t)).ι ≫ e.hom.left := by
  obtain ⟨C, t, he, _, ht, hu⟩ := exists_relative_presentation W I hI hW
  exact ⟨t, ht, hu, integralVariableChangeOverIso W (equation t) C he,
    integralVariableChangeSmoothOverIso W (equation t) C he,
    integralVariableChangeSmoothMap_inclusion W (equation t) C he⟩

end FLT.Mazur.OneGonInfinitesimal
