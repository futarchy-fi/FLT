/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveFinite
public import FLT.Mazur.FiniteCurveEulerIsomorphism

/-!
# Proper curve comparisons that are unchanged on a nonempty open

An unchanged nonempty open gives surjectivity onto an integral proper target.
In positive dimension it also rules out a constant map. Finiteness and equality
of Euler characteristics then recover the original morphism globally.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)]

/-- A proper comparison unchanged over a nonempty open of an integral target is surjective. -/
theorem properComparison_surjective [IsProper f] [IsIntegral Y]
    (hU : (U : Set Y).Nonempty) : Surjective f := by
  have hr : (U : Set Y) ⊆ Set.range f := by
    intro y hy
    obtain ⟨x, hx⟩ := (f ∣_ U).homeomorph.surjective ⟨y, hy⟩
    refine ⟨x.val, ?_⟩
    simpa only [Scheme.Hom.homeomorph_apply, morphismRestrict_base_coe]
      using congrArg Subtype.val hx
  constructor
  apply Set.range_eq_univ.mp
  have hd : DenseRange f := (U.isOpen.dense hU).mono hr
  rw [← f.isClosedMap.isClosed_range.closure_eq]
  exact hd.closure_eq

/-- An unchanged nonempty open prevents a surjective curve map from being constant. -/
theorem openComparison_nonconstant [Nontrivial X] [Surjective f]
    (hU : (U : Set Y).Nonempty) : ∃ x y : X, f x ≠ f y := by
  obtain ⟨z, hz⟩ := hU
  obtain ⟨w, hw⟩ := (Surjective.surj (f := f)) z
  by_contra h
  push Not at h
  have hall (x : X) : f x ∈ U := by rw [h x w, hw]; exact hz
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  apply hxy
  have he : (f ∣_ U) ⟨x, hall x⟩ = (f ∣_ U) ⟨y, hall y⟩ :=
    Subtype.ext (by simpa only [morphismRestrict_base_coe] using h x y)
  exact congrArg Subtype.val ((f ∣_ U).homeomorph.injective he)

/-- Dimension one guarantees that the underlying curve has more than one point. -/
theorem nontrivial_of_dimension_one (hd : topologicalKrullDim X = 1) : Nontrivial X := by
  by_contra h
  let _ := not_nontrivial_iff_subsingleton.mp h
  have hz := topologicalKrullDim_zero_of_discreteTopology X
  rw [hd] at hz
  exact (not_le_of_gt (by norm_num : (0 : WithBot ℕ∞) < 1)) hz

variable {k : Type} [Field k] (g : Y ⟶ Spec (.of k))
  [IsProper g] [IsProper (f ≫ g)] [IsIntegral X] [IsIntegral Y]

/-- An unchanged nonempty open and equal Euler characteristics identify proper integral curves. -/
theorem properCurve_isIso_of_open_euler_eq (hd : topologicalKrullDim X = 1)
    (hU : (U : Set Y).Nonempty)
    (he : curveEulerCharacteristic (f ≫ g) (structureUnitModule X) =
      curveEulerCharacteristic g (structureUnitModule Y)) : IsIso f := by
  let _ : IsProper f := IsProper.of_comp f g
  let _ := properComparison_surjective f U hU
  let _ : Nontrivial X := nontrivial_of_dimension_one hd
  let _ : IsFinite f := nonconstantProperCurveFinite (f ≫ g) g f
    inferInstance inferInstance hd.le inferInstance rfl (openComparison_nonconstant f U hU)
  exact finiteCurve_isIso_of_euler_eq g f hd.le U hU he

end FLT.Mazur.FCurve
