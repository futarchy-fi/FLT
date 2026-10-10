/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelLimit
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Coefficient stages inside a prescribed open neighborhood

An open set containing the image of the original affine base contains the
image of a finite coefficient enlargement. Thus a stable property holding
on that open set holds on the enlarged fixed model. Constructing the open
set for a particular fiber property is a separate geometric obligation.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An open neighborhood of the original base image contains a finite-stage image. -/
theorem exists_coefficient_preimage_open_eq_top {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    (U : (Spec (.of S₀)).Opens)
    (hU : Spec.map (CommRingCat.ofHom S₀.val.toRingHom) ⁻¹ᵁ U = ⊤) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      (coefficientSpectrumToInitial S₀).app i ⁻¹ᵁ U = ⊤ := by
  have (i : (CoefficientStage S₀)ᵒᵖ) :
      CompactSpace ((coefficientSpectrumDiagram S₀).obj i) := by
    change CompactSpace (Spec (.of i.unop.val))
    infer_instance
  let i₀ : (CoefficientStage S₀)ᵒᵖ := .op ⟨S₀, le_rfl, inferInstance⟩
  obtain ⟨i, α, hi⟩ := exists_map_eq_top (coefficientSpectrumDiagram S₀)
    (coefficientSpectrumCone S₀) (coefficientSpectrumIsLimit S₀) (i := i₀) U hU
  exact ⟨i, hi⟩

/-- A stable property on an open neighborhood of the base image holds at a finite stage. -/
theorem exists_coefficient_property_of_open_neighborhood {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of S₀)) (U : (Spec (.of S₀)).Opens)
    (hU : Spec.map (CommRingCat.ofHom S₀.val.toRingHom) ⁻¹ᵁ U = ⊤)
    (W : MorphismProperty Scheme.{u}) [W.IsStableUnderBaseChange] [W.RespectsIso]
    (hW : W (p ∣_ U)) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      W (pullback.snd p ((coefficientSpectrumToInitial S₀).app i)) := by
  obtain ⟨i, hi⟩ := exists_coefficient_preimage_open_eq_top S₀ U hU
  let b := (coefficientSpectrumToInitial S₀).app i
  have hb : Set.range b ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact Set.range_subset_iff.mpr fun x ↦ hi.ge (Set.mem_univ x)
  let a := IsOpenImmersion.lift U.ι b hb
  have ha : a ≫ U.ι = b := IsOpenImmersion.lift_fac _ _ _
  have hcart := (IsPullback.of_hasPullback (p ∣_ U) a).paste_horiz
    (isPullback_morphismRestrict p U).flip
  rw [ha] at hcart
  have hWa : W (pullback.snd (p ∣_ U) a) :=
    W.of_isPullback (IsPullback.of_hasPullback (p ∣_ U) a) hW
  refine ⟨i, ?_⟩
  rwa [← W.cancel_left_of_respectsIso hcart.isoPullback.hom, hcart.isoPullback_hom_snd]

end FLT.Mazur.Approximation
