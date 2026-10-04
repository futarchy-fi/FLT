/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveIdealTwistDegree

/-!
# Sections of positive-degree line powers

The proved Euler-characteristic formulas force unbounded H⁰ in positive powers,
including twists by any nonzero coherent ideal. The resulting sections are
actual global sections; affineness of their generator opens is a separate issue.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- A positive Euler-characteristic slope forces unbounded H⁰ in positive indices. -/
theorem h0_unbounded_of_euler_formula (M : ℕ → X.Modules) (d c : ℤ) (hd : 0 < d)
    (h : ∀ n, curveEulerCharacteristic f (M n) = (n : ℤ) * d + c) (b : ℕ) :
    ∃ n : ℕ, 0 < n ∧ b < Module.finrank k (ModuleScalarH f (M n) 0) := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((b : ℤ) - c)
  refine ⟨m + 1, by omega, ?_⟩
  have hg := h (m + 1)
  unfold curveEulerCharacteristic at hg
  have hp : (1 : ℤ) ≤ d := hd
  have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
  have hq : (0 : ℤ) ≤ Module.finrank k (ModuleScalarH f (M (m + 1)) 1) :=
    Nat.cast_nonneg _
  push_cast at hg
  have : (b : ℤ) < (Module.finrank k (ModuleScalarH f (M (m + 1)) 0) : ℤ) := by
    nlinarith
  exact_mod_cast this

/-- Positive H⁰ dimension supplies a nonzero actual global section. -/
theorem exists_nonzero_section_of_h0_pos (M : X.Modules)
    (h : 0 < Module.finrank k (ModuleScalarH f M 0)) : ∃ s : Γ(M, ⊤), s ≠ 0 := by
  have : Nontrivial (ModuleScalarH f M 0) := Module.nontrivial_of_finrank_pos h
  obtain ⟨s, hs⟩ := exists_ne (0 : ModuleScalarH f M 0)
  exact ⟨moduleScalarH0Equiv f M s, fun h ↦ hs ((moduleScalarH0Equiv f M).map_eq_zero_iff.mp h)⟩

variable [IsIntegral X] [IsProper f] (hd : topologicalKrullDim X ≤ 1)

include hd in
/-- An arbitrary positive-degree line has unbounded H⁰ in its positive tensor powers. -/
theorem line_power_h0_unbounded {L : X.Modules} (hL : LocallyFreeRankOne L)
    (hdeg : 0 < curveSheafDegree f L) (b : ℕ) :
    ∃ n : ℕ, 0 < n ∧ b < Module.finrank k (ModuleScalarH f (tensorPower L n) 0) :=
  h0_unbounded_of_euler_formula f (tensorPower L) _ _ hdeg
    (curveEulerCharacteristic_line_power f hd hL) b

include hd in
/-- A positive-degree line has a nonzero section in a positive tensor power. -/
theorem exists_nonzero_line_power_section {L : X.Modules} (hL : LocallyFreeRankOne L)
    (hdeg : 0 < curveSheafDegree f L) :
    ∃ (n : ℕ), 0 < n ∧ ∃ s : Γ(tensorPower L n, ⊤), s ≠ 0 := by
  obtain ⟨n, hn, hs⟩ := line_power_h0_unbounded f hd hL hdeg 0
  exact ⟨n, hn, exists_nonzero_section_of_h0_pos f _ hs⟩

include hd in
/-- Imposing any nonzero ideal still leaves unbounded sections in positive line powers. -/
theorem ideal_line_power_h0_unbounded (I : X.IdealSheafData) (hI : I ≠ ⊥)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (hdeg : 0 < curveSheafDegree f L) (b : ℕ) :
    ∃ n : ℕ, 0 < n ∧ b < Module.finrank k
      (ModuleScalarH f (tensor (idealModule I) (tensorPower L n)) 0) :=
  h0_unbounded_of_euler_formula f (fun n ↦ tensor (idealModule I) (tensorPower L n)) _ _ hdeg
    (curveEulerCharacteristic_ideal_line_power f hd I hI hL) b

include hd in
/-- There is a nonzero positive-power section with any prescribed nonzero ideal coefficient. -/
theorem exists_nonzero_ideal_line_power_section (I : X.IdealSheafData) (hI : I ≠ ⊥)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (hdeg : 0 < curveSheafDegree f L) :
    ∃ (n : ℕ), 0 < n ∧ ∃ s : Γ(tensor (idealModule I) (tensorPower L n), ⊤), s ≠ 0 := by
  obtain ⟨n, hn, hs⟩ := ideal_line_power_h0_unbounded f hd I hI hL hdeg 0
  exact ⟨n, hn, exists_nonzero_section_of_h0_pos f _ hs⟩

end FLT.Mazur.FCurve
