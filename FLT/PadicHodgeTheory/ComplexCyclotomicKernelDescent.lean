/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexRelativeAxDescent
public import FLT.PadicHodgeTheory.ComplexCyclotomicClosure
public import FLT.PadicHodgeTheory.PadicCyclotomicKernel

/-! # Unconditional descent for the actual cyclotomic-character kernel -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Kernel invariants in the original C_p descend to the actual completed cyclotomic union. -/
theorem complexCyclotomic_kernel_fixed_mem_closure (x : ℂ_[p])
    (hx : ∀ σ : PadicGalois p,
      cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1 → complexGalois p σ x = x) :
    x ∈ complexCyclotomicClosure p := by
  apply (mem_complexCyclotomicClosure p x).mpr
  apply complexRelativeGalois_fixed_mem_closure p (padicCyclotomicUnion p) x
  intro σ
  apply hx
  apply padicCyclotomic_character_eq_one_of_fixes_union p
  intro b
  exact σ.commutes b

/-- Every vector of the completed union is fixed by the actual character kernel. -/
theorem complexCyclotomic_kernel_fixed_of_mem_closure (x : ℂ_[p])
    (hx : x ∈ complexCyclotomicClosure p) (σ : PadicGalois p)
    (hσ : cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1) :
    complexGalois p σ x = x := by
  let τ : Gal(PadicAlgCl p/padicCyclotomicUnion p) :=
    { σ.toRingEquiv with commutes' := padicCyclotomic_kernel_fixes_union p σ hσ }
  exact complexRelativeGalois_fixed_of_mem_closure p (padicCyclotomicUnion p) x
    ((mem_complexCyclotomicClosure p x).mp hx) τ

/-- The completed cyclotomic union is exactly the kernel-fixed subspace of the original C_p. -/
theorem complexCyclotomic_kernel_fixed_iff (x : ℂ_[p]) :
    (∀ σ : PadicGalois p,
      cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv = 1 → complexGalois p σ x = x) ↔
        x ∈ complexCyclotomicClosure p :=
  ⟨complexCyclotomic_kernel_fixed_mem_closure p x,
    fun hx σ hσ ↦ complexCyclotomic_kernel_fixed_of_mem_closure p x hx σ hσ⟩

end PadicHodgeTheory
