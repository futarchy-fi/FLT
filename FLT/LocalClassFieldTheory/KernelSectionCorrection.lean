/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.KernelMixedCocycle
public import Mathlib.Tactic.LinearCombination

/-!
# Correcting mixed terms using a quotient section

The cochain is constructed from the kernel component of each group element
and a principal witness for the mixed crossed homomorphism at its representative.
No topological section is asserted here.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable {G H M : Type*} [Group G] [Group H] [AddCommGroup M] [DistribMulAction G M]

/-- A surjective group homomorphism admits a section preserving the identity. -/
theorem exists_normalized_section (f : G →* H) (hf : Function.Surjective f) :
    ∃ s : H → G, (∀ q, f (s q) = q) ∧ s 1 = 1 := by
  classical
  refine ⟨fun q => if q = 1 then 1 else (hf q).choose, ?_, by simp⟩
  intro q
  dsimp only
  split_ifs with h
  · simp [h]
  · exact (hf q).choose_spec

/-- The kernel component relative to a section. -/
def sectionKernel (f : G →* H) (s : H → G) (hs : ∀ q, f (s q) = q) (g : G) : f.ker :=
  ⟨g * (s (f g))⁻¹, by simp [MonoidHom.mem_ker, hs]⟩

/-- The explicitly constructed correcting cochain. -/
def sectionCorrection (f : G →* H) (s : H → G) (hs : ∀ q, f (s q) = q)
    (c : G × G → M) (a : H → M) (g : G) : M :=
  (sectionKernel f s hs g : G) • a (f g) - c (sectionKernel f s hs g, s (f g))

variable (f : G →* H) (s : H → G) (hs : ∀ q, f (s q) = q) (hs1 : s 1 = 1)
  (c : G × G → M) (hc : IsCocycle₂ c) (hN : ∀ n m : f.ker, c (n, m) = 0)
  (a : H → M) (ha1 : a 1 = 0)

include hs1 hc hN ha1

/-- The correcting cochain vanishes on the kernel. -/
theorem sectionCorrection_kernel (n : f.ker) : sectionCorrection f s hs c a n = 0 := by
  simp only [sectionCorrection, sectionKernel, (show f (n : G) = 1 from n.property),
    hs1, ha1, smul_zero,
    inv_one, mul_one, kernel_zero_twoCocycle_one_right f.ker c hc hN, sub_self]

omit hs1 ha1 in
/-- The correcting cochain takes the chosen witness at each representative. -/
theorem sectionCorrection_section (q : H) : sectionCorrection f s hs c a (s q) = a q := by
  simp only [sectionCorrection, sectionKernel, hs, mul_inv_cancel, one_smul,
    kernel_zero_twoCocycle_one_left f.ker c hc hN, sub_zero]

omit hs1 ha1 in
/-- Left multiplication by the kernel obeys the desired correction equation. -/
theorem sectionCorrection_mul_left (n : f.ker) (g : G) :
    sectionCorrection f s hs c a (n * g) =
      (n : G) • sectionCorrection f s hs c a g - c (n, g) := by
  let k := sectionKernel f s hs g
  have hk : (k : G) * s (f g) = g := by simp [k, sectionKernel, mul_assoc]
  have he := hc n k (s (f g))
  rw [hN, add_zero, hk] at he
  simp only [sectionCorrection, sectionKernel, map_mul, (show f (n : G) = 1 from n.property),
    one_mul,
    smul_sub, ← mul_smul]
  change ((n : G) * g * (s (f g))⁻¹) • a (f g) -
      c ((n : G) * g * (s (f g))⁻¹, s (f g)) =
    ((n : G) * (k : G)) • a (f g) - (n : G) • c (k, s (f g)) - c (n, g)
  rw [mul_assoc]
  change ((n : G) * k) • a (f g) - c ((n : G) * k, s (f g)) = _
  rw [he]
  abel

/-- The correction kills all mixed terms having a kernel element on the left. -/
theorem sectionCorrection_zero_left (n : f.ker) (g : G) :
    correctTwoCocycle c (sectionCorrection f s hs c a) (n, g) = 0 := by
  dsimp only [correctTwoCocycle]
  rw [sectionCorrection_mul_left f s hs c hc hN a,
    sectionCorrection_kernel f s hs hs1 c hc hN a ha1]
  abel

/-- Principal mixed witnesses kill the remaining mixed terms at representatives. -/
theorem sectionCorrection_zero_section_right
    (ha : ∀ q n, kernelMixedCocycle f c (s q) n = (n : G) • a q - a q)
    (q : H) (n : f.ker) :
    correctTwoCocycle c (sectionCorrection f s hs c a) (s q, n) = 0 := by
  let m : f.ker := ⟨s q * n * (s q)⁻¹, by
    simp [MonoidHom.mem_ker, (show f (n : G) = 1 from n.property)]⟩
  have hm : (m : G) * s q = s q * n := by simp [m, mul_assoc]
  have hm' : kernelConjugate f (s q) m = n := by
    apply Subtype.ext
    simp [kernelConjugate, m, mul_assoc]
  have he := ha q m
  simp only [kernelMixedCocycle, hm'] at he
  dsimp only [correctTwoCocycle]
  rw [sectionCorrection_kernel f s hs hs1 c hc hN a ha1, smul_zero, ← hm,
    sectionCorrection_mul_left f s hs c hc hN a,
    sectionCorrection_section f s hs c hc hN a]
  linear_combination (norm := abel) -he

/-- The cocycle equation propagates right vanishing from representatives to the group. -/
theorem sectionCorrection_zero_right
    (ha : ∀ q n, kernelMixedCocycle f c (s q) n = (n : G) • a q - a q)
    (g : G) (n : f.ker) :
    correctTwoCocycle c (sectionCorrection f s hs c a) (g, n) = 0 := by
  let k := sectionKernel f s hs g
  have hk : (k : G) * s (f g) = g := by simp [k, sectionKernel, mul_assoc]
  have he := correctTwoCocycle_isCocycle c hc (sectionCorrection f s hs c a)
    k (s (f g)) n
  rw [hk, sectionCorrection_zero_left f s hs hs1 c hc hN a ha1,
    sectionCorrection_zero_left f s hs hs1 c hc hN a ha1,
    sectionCorrection_zero_section_right f s hs hs1 c hc hN a ha1 ha,
    smul_zero, add_zero, add_zero] at he
  exact he

end LocalClassFieldTheory
