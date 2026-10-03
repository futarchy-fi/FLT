/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.KernelSectionCorrection

/-!
# Descending a cocycle with zero mixed terms

The cocycle identity proves constancy on both quotient fibers and invariance
of every value. A section then gives the unique descended cocycle.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable {G H M : Type*} [Group G] [Group H] [AddCommGroup M] [DistribMulAction G M]
  (f : G →* H) (c : G × G → M) (hc : IsCocycle₂ c)
  (hl : ∀ n : f.ker, ∀ g, c (n, g) = 0) (hr : ∀ g, ∀ n : f.ker, c (g, n) = 0)

include hc hr

/-- A cocycle with zero right mixed terms is constant on second-coordinate fibers. -/
theorem kernelCocycle_fiber_right (g h h' : G) (hh : f h = f h') :
    c (g, h) = c (g, h') := by
  let n : f.ker := ⟨h⁻¹ * h', by simp [MonoidHom.mem_ker, ← hh]⟩
  have hn : h * (n : G) = h' := by simp [n]
  have he := hc g h n
  rw [hr, hr, zero_add, smul_zero, zero_add, hn] at he
  exact he

include hl

/-- Vanishing of both mixed terms also gives constancy on first-coordinate fibers. -/
theorem kernelCocycle_fiber_left (g g' h : G) (hg : f g = f g') :
    c (g, h) = c (g', h) := by
  let n : f.ker := ⟨g⁻¹ * g', by simp [MonoidHom.mem_ker, ← hg]⟩
  have hn : g * (n : G) = g' := by simp [n]
  have he := hc g n h
  rw [hr, hl, add_zero, smul_zero, zero_add, hn] at he
  rw [he]
  exact kernelCocycle_fiber_right f c hc hr g h (n * h) (by
    simp [show f (n : G) = 1 from n.property])

/-- Every value of the descended cocycle is fixed by the kernel. -/
theorem kernelCocycle_fixed (g h : G) (n : f.ker) : (n : G) • c (g, h) = c (g, h) := by
  have he := hc n g h
  rw [hl, hl, add_zero, add_zero] at he
  rw [← he]
  exact (kernelCocycle_fiber_left f c hc hl hr g (n * g) h (by
    simp [show f (n : G) = 1 from n.property])).symm

omit hc hl hr [AddCommGroup M] [DistribMulAction G M] in
/-- Surjective pullback and an injective coefficient map determine a cochain uniquely. -/
theorem descendedTwoCochain_unique {P : Type*} (hf : Function.Surjective f)
    (i : P → M) (hi : Function.Injective i) (a b : H × H → P)
    (ha : ∀ g h, i (a (f g, f h)) = c (g, h))
    (hb : ∀ g h, i (b (f g, f h)) = c (g, h)) : a = b := by
  funext p
  obtain ⟨g, hg⟩ := hf p.1
  obtain ⟨h, hh⟩ := hf p.2
  apply hi
  simpa only [hg, hh] using (ha g h).trans (hb g h).symm

/-- Descend the corrected cocycle into the actual invariant coefficient group. -/
theorem exists_descended_twoCocycle {P : Type*} [AddCommGroup P] [DistribMulAction H P]
    (hf : Function.Surjective f) (i : P →+ M) (hi : Function.Injective i)
    (heq : ∀ g p, i (f g • p) = g • i p)
    (hfix : ∀ m : M, (∀ n : f.ker, (n : G) • m = m) → ∃ p, i p = m) :
    ∃ d : H × H → P, IsCocycle₂ d ∧ ∀ g h, i (d (f g, f h)) = c (g, h) := by
  classical
  obtain ⟨s, hs, _⟩ := exists_normalized_section f hf
  have hv (p : H × H) : ∃ v, i v = c (s p.1, s p.2) :=
    hfix _ (kernelCocycle_fixed f c hc hl hr _ _)
  let d : H × H → P := fun p => (hv p).choose
  have hd (g h : G) : i (d (f g, f h)) = c (g, h) := by
    calc
      _ = c (s (f g), s (f h)) := (hv _).choose_spec
      _ = c (g, s (f h)) := kernelCocycle_fiber_left f c hc hl hr _ _ _ (hs _)
      _ = c (g, h) := kernelCocycle_fiber_right f c hc hr _ _ _ (hs _)
  refine ⟨d, ?_, hd⟩
  intro g h j
  obtain ⟨g, rfl⟩ := hf g
  obtain ⟨h, rfl⟩ := hf h
  obtain ⟨j, rfl⟩ := hf j
  apply hi
  simp only [map_add, heq, ← map_mul, hd]
  exact hc g h j

end LocalClassFieldTheory
