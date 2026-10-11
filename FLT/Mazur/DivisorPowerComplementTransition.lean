/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementFiltration

/-!
# Cohomological pole transitions retain their actual complement functions

The previously constructed injective H0 maps agree with the canonical
section transitions used in the multiplicative function filtration.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- Degree-zero cohomology defines its original function on the divisor complement. -/
def divisorPowerH0Function (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 0) :
    Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤) :=
  divisorComplementFunction hI m (moduleScalarH0Equiv f _ x)

/-- The actual injective cohomological pole transition preserves the represented function. -/
theorem divisorPowerH0Function_step (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 0) :
    divisorPowerH0Function f hI (m + 1) (divisorPowerH0Step f hI m x) =
      divisorPowerH0Function f hI m x := by
  unfold divisorPowerH0Function
  rw [divisorPowerH0Step_sections, divisorTwistedComplex_leftUnitor,
    divisorComplementFunction_cons]

/-- The function filtration is exactly the image of the actual degree-zero cohomology. -/
theorem mem_divisorPoleFunctions_iff_h0 (m : ℕ)
    (a : Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤)) :
    a ∈ divisorPoleFunctions hI m ↔ ∃ x, divisorPowerH0Function f hI m x = a := by
  rw [mem_divisorPoleFunctions]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(moduleScalarH0Equiv f _).symm s, ?_⟩
    simpa only [divisorPowerH0Function, LinearEquiv.apply_symm_apply] using hs
  · rintro ⟨x, hx⟩
    exact ⟨moduleScalarH0Equiv f _ x, hx⟩

/-- A canonical pole-space transition also retains membership in the lower function space. -/
theorem divisorPowerH0Function_step_mem (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 0) :
    divisorPowerH0Function f hI (m + 1) (divisorPowerH0Step f hI m x) ∈
      divisorPoleFunctions hI m := by
  rw [divisorPowerH0Function_step]
  exact (mem_divisorPoleFunctions_iff_h0 f hI m _).mpr ⟨x, rfl⟩

end FLT.Mazur.FCurve
