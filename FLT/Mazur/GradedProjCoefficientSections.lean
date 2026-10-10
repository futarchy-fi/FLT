/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjLineTransitionEvaluation

/-!
# Global coordinate sections of the coefficient line

Equal-degree homogeneous coordinates define actual sections of the descended
coefficient line, retaining their fractions on each original chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.GradedProjLine

open FCurve.ModuleSheafUnitCocycle

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- The coordinate multiplication law holds already on a pairwise overlap. -/
theorem coordinate_pair_mul (i j k : ι) :
    toOverlap 𝒜 f hf i j (coordinate 𝒜 f hf i j) *
        awayMap 𝒜 (hf i) (mul_comm (f i) (f j)) (coordinate 𝒜 f hf j k) =
      toOverlap 𝒜 f hf i j (coordinate 𝒜 f hf i k) := by
  simp only [toOverlap, coordinate, awayMap_mk]
  apply val_injective
  simp only [val_mul, Away.val_mk, pow_one, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- Restriction of a chart fraction to any subopen of a product chart. -/
theorem awayToSection_restrict {s t x : A} {e : ℕ} (ht : t ∈ 𝒜 e)
    (hx : x = s * t) (V : (Proj 𝒜).Opens)
    (hV : V ≤ Proj.basicOpen 𝒜 x) (z : Away 𝒜 s) :
    (Proj 𝒜).presheaf.map
        (homOfLE (hV.trans (Proj.basicOpen_mono 𝒜 s x ⟨t, hx⟩))).op
        (Proj.awayToSection 𝒜 s z) =
      (Proj 𝒜).presheaf.map (homOfLE hV).op
        (Proj.awayToSection 𝒜 x (awayMap 𝒜 ht hx z)) := by
  have he := congrArg (fun g ↦ g ≫ (Proj 𝒜).presheaf.map (homOfLE hV).op)
    (Proj.awayMap_awayToSection 𝒜 ht hx)
  simp only [Category.assoc, ← Functor.map_comp] at he
  exact (ConcreteCategory.congr_hom he z).symm

/-- The actual coordinate functions obey the descended line's transition equation. -/
theorem coordinate_section_transition (i j k : ι) (V : (Proj 𝒜).Opens)
    (hi : V ≤ chart 𝒜 f i) (hj : V ≤ chart 𝒜 f j) :
    (Proj 𝒜).presheaf.map (homOfLE hi).op
        (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i k)) =
      ((cocycle 𝒜 f hf 1).unit i j V hi hj : Γ(Proj 𝒜, V)) *
        (Proj 𝒜).presheaf.map (homOfLE hj).op
          (Proj.awayToSection 𝒜 (f j) (coordinate 𝒜 f hf j k)) := by
  have hV : V ≤ Proj.basicOpen 𝒜 (f i * f j) := by
    rw [Proj.basicOpen_mul]
    exact le_inf hi hj
  rw [coefficient_unit_eq]
  erw [awayToSection_restrict 𝒜 (hf j) rfl V hV,
    awayToSection_restrict 𝒜 (hf j) rfl V hV,
    awayToSection_restrict 𝒜 (hf i) (mul_comm (f i) (f j)) V hV]
  rw [← map_mul, ← map_mul]
  exact congrArg (fun z : Away 𝒜 (f i * f j) ↦
    (Proj 𝒜).presheaf.map (homOfLE hV).op (Proj.awayToSection 𝒜 (f i * f j) z))
    (coordinate_pair_mul 𝒜 f hf i j k).symm

/-- Each original homogeneous coordinate gives a global section of the coefficient line. -/
def coefficientSection (k : ι) : Γ(line 𝒜 f hf 1, ⊤) :=
  ⟨fun i ↦ (Proj 𝒜).presheaf.map (homOfLE inf_le_right).op
    (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i k)), by
    intro i j V hi hj
    change (Proj 𝒜).presheaf.map (homOfLE hi).op
      ((Proj 𝒜).presheaf.map (homOfLE inf_le_right).op _) =
        _ * (Proj 𝒜).presheaf.map (homOfLE hj).op
          ((Proj 𝒜).presheaf.map (homOfLE inf_le_right).op _)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact coordinate_section_transition 𝒜 f hf i j k V
      (hi.trans inf_le_right) (hj.trans inf_le_right)⟩

/-- The global coordinate retains its specified ratio on every chart subopen. -/
theorem coefficientSection_evaluate (i k : ι) (V : (Proj 𝒜).Opens)
    (hi : V ≤ chart 𝒜 f i) :
    (cocycle 𝒜 f hf 1).evaluate i hi
        ((line 𝒜 f hf 1).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
          (coefficientSection 𝒜 f hf k)) =
      (Proj 𝒜).presheaf.map (homOfLE hi).op
        (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i k)) := by
  change res _ (res _ (res _ _)) = _
  rw [res_res, res_res]

/-- Its own coordinate is exactly the unit generator, on every chart subopen. -/
theorem coefficientSection_evaluate_self (i : ι) (V : (Proj 𝒜).Opens)
    (hi : V ≤ chart 𝒜 f i) :
    (cocycle 𝒜 f hf 1).evaluate i hi
        ((line 𝒜 f hf 1).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
          (coefficientSection 𝒜 f hf i)) = 1 := by
  rw [coefficientSection_evaluate, coordinate_self, map_one, map_one]

end FLT.Mazur.GradedProjLine
