/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.KernelCocycleNormalization

/-!
# The crossed homomorphism of mixed terms

For a cocycle vanishing on the kernel square, compare the two ways to move
a kernel element past an arbitrary group element.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable {G H M : Type*} [Group G] [Group H] [AddCommGroup M] [DistribMulAction G M]

/-- Conjugation by the inverse of a group element preserves a homomorphism kernel. -/
def kernelConjugate (f : G →* H) (g : G) (n : f.ker) : f.ker :=
  ⟨g⁻¹ * n * g, by simp [MonoidHom.mem_ker, (show f (n : G) = 1 from n.property)]⟩

/-- The difference between the two mixed terms. -/
def kernelMixedCocycle (f : G →* H) (c : G × G → M) (g : G) (n : f.ker) : M :=
  c (n, g) - c (g, kernelConjugate f g n)

/-- The mixed-term difference is a crossed homomorphism on the kernel. -/
theorem kernelMixedCocycle_isCocycle (f : G →* H) (c : G × G → M)
    (hc : IsCocycle₂ c) (hN : ∀ n m : f.ker, c (n, m) = 0) (g : G) :
    IsCocycle₁ (kernelMixedCocycle f c g) := by
  intro n m
  let n' := kernelConjugate f g n
  let m' := kernelConjugate f g m
  have hn : g * (n' : G) = n * g := by simp [n', kernelConjugate, mul_assoc]
  have hm : g * (m' : G) = m * g := by simp [m', kernelConjugate, mul_assoc]
  have hnm : (kernelConjugate f g (n * m) : G) = n' * m' := by
    simp [n', m', kernelConjugate, mul_assoc]
  have h₁ := hc n m g
  rw [hN, add_zero] at h₁
  have h₂ := hc n g m'
  rw [hm] at h₂
  have h₃ := hc g n' m'
  rw [hN, smul_zero, zero_add, hn] at h₃
  change c ((n : G) * m, g) - c (g, kernelConjugate f g (n * m)) =
    (n : G) • (c (m, g) - c (g, m')) + (c (n, g) - c (g, n'))
  rw [hnm, h₁, ← h₃, smul_sub]
  have h₂' : c (n, (m : G) * g) =
      c ((n : G) * g, m') + c (n, g) - (n : G) • c (g, m') := by
    rw [h₂]
    abel
  rw [h₂']
  abel

/-- At the identity representative the mixed crossed homomorphism is zero. -/
theorem kernelMixedCocycle_one (f : G →* H) (c : G × G → M)
    (hc : IsCocycle₂ c) (hN : ∀ n m : f.ker, c (n, m) = 0) :
    kernelMixedCocycle f c 1 = 0 := by
  funext n
  simp only [kernelMixedCocycle, kernelConjugate, inv_one, one_mul, mul_one,
    kernel_zero_twoCocycle_one_left f.ker c hc hN,
    kernel_zero_twoCocycle_one_right f.ker c hc hN, sub_self, Pi.zero_apply]

end LocalClassFieldTheory
