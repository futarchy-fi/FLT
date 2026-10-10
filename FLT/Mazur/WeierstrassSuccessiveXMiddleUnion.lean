/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleIncidence
public import FLT.Mazur.WeierstrassModificationXConicRegular

/-!
# The scheme-theoretic union of the conic and two attached lines

The three restriction maps jointly detect every middle-fiber function.
Thus the closed cover has no hidden nilpotent thickening or omitted ideal:
the intersection of its three actual component ideals is zero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "T" => coord W 0 0 0 0 c 0
local notation "V" => coord W 0 0 0 0 c 1
local notation "U" => coord W 0 0 0 0 c 2

include h2 in
/-- The conic and full incidence boundary have zero ideal intersection. -/
theorem middle_conic_boundary_inf :
    Ideal.span {U} ⊓ Ideal.span {T} = (⊥ : Ideal A) := by
  apply le_antisymm ?_ bot_le
  intro z hz
  rw [Ideal.mem_bot]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hz.2
  have hz0 : middleConicMap W c h2 z = 0 := by
    change z ∈ RingHom.ker (middleConicMap W c h2)
    rw [middleConicMap_ker]
    exact hz.1
  have hd0 : middleConicMap W c h2 d = 0 := by
    apply (conicT_regular W.a₁ c).left
    simpa only [hd, map_mul, middleConicMap_coord, Matrix.cons_val_zero, mul_zero] using hz0
  have hdmem : d ∈ Ideal.span {U} := by
    rw [← middleConicMap_ker W c h2]
    exact hd0
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hdmem
  rw [hd, hb, ← mul_assoc, incidence, map_zero, zero_mul]

include h2 in
/-- The ordered line ideals intersect in precisely the full incidence boundary ideal. -/
theorem middle_line_ideals_inf (ha : IsUnit W.a₁) :
    middleLineIdeal W c 0 ⊓ middleLineIdeal W c (-W.a₁) = Ideal.span {T} := by
  have h0 : middleLineIdeal W c 0 = Ideal.span {T, V} := by simp [middleLineIdeal]
  have h1 : middleLineIdeal W c (-W.a₁) =
      Ideal.span {T, V + algebraMap R A W.a₁} := by simp [middleLineIdeal]
  have ht : T ∈ Ideal.span ({T} : Set A) := Ideal.subset_span (Set.mem_singleton _)
  apply le_antisymm
  · rw [← Ideal.mul_eq_inf_of_coprime (middle_lines_disjoint W c ha), h0, h1,
      Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Ideal.mul_mem_left _ _ ht
    · exact Ideal.mul_mem_right _ _ ht
    · exact Ideal.mul_mem_left _ _ ht
    · rw [sub_eq_zero.mp (middle_conic_relation W c h2), pow_two]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ht)
  · apply le_inf
    all_goals
      apply Ideal.span_le.mpr
      rw [Set.singleton_subset_iff]
      exact Ideal.subset_span (Set.mem_insert _ _)

include h2 in
/-- The three actual component ideals have zero intersection, scheme-theoretically. -/
theorem middle_component_ideals_inf (ha : IsUnit W.a₁) :
    Ideal.span {U} ⊓ (middleLineIdeal W c 0 ⊓ middleLineIdeal W c (-W.a₁)) =
      (⊥ : Ideal A) := by
  rw [middle_line_ideals_inf W c h2 ha, middle_conic_boundary_inf W c h2]

/-- Vanishing on the conic and both original tangent lines forces the whole function to vanish. -/
theorem middle_components_detect_zero (ha : IsUnit W.a₁) (z : A)
    (hc : middleConicMap W c h2 z = 0)
    (h0 : middleLineMap W c h2 0 (middle_first_root W) z = 0)
    (h1 : middleLineMap W c h2 (-W.a₁) (middle_second_root W) z = 0) : z = 0 := by
  have hz : z ∈ Ideal.span {U} ⊓
      (middleLineIdeal W c 0 ⊓ middleLineIdeal W c (-W.a₁)) := by
    rw [← middleConicMap_ker W c h2,
      ← middleLineMap_ker W c h2 0 (middle_first_root W),
      ← middleLineMap_ker W c h2 (-W.a₁) (middle_second_root W)]
    exact ⟨hc, h0, h1⟩
  rwa [middle_component_ideals_inf W c h2 ha, Ideal.mem_bot] at hz

end FLT.Mazur.WeierstrassSuccessiveX
