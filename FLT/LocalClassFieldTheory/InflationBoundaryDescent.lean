/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormalizedTwoCocycles

/-!
# Descent of normalized inflation boundaries

A bounding one-cochain that vanishes on the kernel is constant on quotient
fibers and takes invariant values. Its descended cochain is continuous.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open GaloisRepresentation.Extensions

variable {G H M P : Type*} [Group G] [Group H]
  [AddCommGroup M] [AddCommGroup P] [DistribMulAction G P]
  (f : G →* H) (i : M →+ P) (c : H × H → M) (b : G → P)
  (hb : ∀ g h, g • b h - b (g * h) + b g = i (c (f g, f h)))
  (hb0 : ∀ n, f n = 1 → b n = 0)
  (hc0 : ∀ h, c (h, 1) = 0) (hc1 : ∀ h, c (1, h) = 0)

include hb hb0 hc0

/-- A normalized bounding cochain is unchanged by right multiplication by the kernel. -/
theorem inflationBoundary_mul_kernel (g n : G) (hn : f n = 1) :
    b (g * n) = b g := by
  have he := hb g n
  rw [hn, hc0, map_zero, hb0 n hn, smul_zero, zero_sub] at he
  exact neg_add_eq_zero.mp he

/-- Vanishing on the kernel forces constancy on every fiber of the quotient map. -/
theorem inflationBoundary_fiber (g h : G) (hgh : f g = f h) : b g = b h := by
  have hn : f (g⁻¹ * h) = 1 := by rw [map_mul, map_inv, hgh, inv_mul_cancel]
  simpa only [mul_inv_cancel_left] using
    (inflationBoundary_mul_kernel f i c b hb hb0 hc0 g (g⁻¹ * h) hn).symm

include hc1

/-- A normalized bounding cochain has kernel-invariant values. -/
theorem inflationBoundary_fixed (g n : G) (hn : f n = 1) : n • b g = b g := by
  have he := hb n g
  rw [hn, hc1, map_zero, hb0 n hn, add_zero] at he
  have hfiber := inflationBoundary_fiber f i c b hb hb0 hc0 (n * g) g
    (by rw [map_mul, hn, one_mul])
  exact (sub_eq_zero.mp he).trans hfiber

variable [DistribMulAction H M] [TopologicalSpace G] [TopologicalSpace H]
  [TopologicalSpace M] [TopologicalSpace P] [DiscreteTopology P]

/-- Continuous descent across a quotient, including the actual boundary equation. -/
theorem exists_descended_inflationBoundary (hf : Topology.IsQuotientMap f)
    (hi : Function.Injective i) (heq : ∀ g m, i (f g • m) = g • i m)
    (hfix : ∀ p : P, (∀ n, f n = 1 → n • p = p) → ∃ m, i m = p)
    (hbcont : Continuous b) :
    ∃ d : C(H, M), ∀ g h, g • d h - d (g * h) + d g = c (g, h) := by
  classical
  choose a ha using fun g => hfix (b g) (inflationBoundary_fixed f i c b hb hb0 hc0 hc1 g)
  have hafiber : ∀ g h, f g = f h → a g = a h := by
    intro g h hgh
    apply hi
    rw [ha, ha]
    exact inflationBoundary_fiber f i c b hb hb0 hc0 g h hgh
  let d : H → M := fun h => a (hf.surjective.hasRightInverse.choose h)
  have hd : ∀ g, d (f g) = a g := fun g =>
    hafiber _ g (hf.surjective.hasRightInverse.choose_spec (f g))
  have hacont : Continuous a := by
    let j : P → M := Function.invFun i
    have hj : j ∘ b = a := by
      funext g
      change Function.invFun i (b g) = a g
      rw [← ha g, Function.leftInverse_invFun hi]
    rw [← hj]
    exact continuous_of_discreteTopology.comp hbcont
  have hdcont : Continuous d := hf.continuous_iff.mpr (by
    convert hacont using 1
    exact funext hd)
  refine ⟨⟨d, hdcont⟩, ?_⟩
  intro g h
  obtain ⟨x, rfl⟩ := hf.surjective g
  obtain ⟨y, rfl⟩ := hf.surjective h
  apply hi
  change i (f x • d (f y) - d (f x * f y) + d (f x)) = _
  rw [← map_mul, hd, hd, hd, map_add, map_sub, heq, ha, ha, ha]
  exact hb x y

end LocalClassFieldTheory
