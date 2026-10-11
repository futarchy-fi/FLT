/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementCanonical

/-!
# The multiplicative filtration of actual complement functions

The degree-m piece is the image of the original global pole sections.
Canonical transitions make these images increasing, and actual tensor
multiplication respects addition of pole bounds.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- The function construction as an additive homomorphism. -/
def divisorComplementAddHom (m : ℕ) :
    Γ(tensorPower (divisorLineBundle I hI) m, ⊤) →+
      Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤) where
  toFun := divisorComplementFunction hI m
  map_zero' := divisorComplementFunction_zero hI m
  map_add' := divisorComplementFunction_add hI m

/-- Functions represented by original sections with pole bound m. -/
def divisorPoleFunctions (m : ℕ) :
    AddSubgroup Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤) :=
  (divisorComplementAddHom hI m).range

/-- A pole bound means existence of an actual global section with that function. -/
theorem mem_divisorPoleFunctions (m : ℕ)
    (a : Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤)) :
    a ∈ divisorPoleFunctions hI m ↔ ∃ s, divisorComplementFunction hI m s = a := Iff.rfl

/-- Canonical pole transitions make successive function spaces nested. -/
theorem divisorPoleFunctions_le_succ (m : ℕ) :
    divisorPoleFunctions hI m ≤ divisorPoleFunctions hI (m + 1) := by
  rintro a ⟨s, rfl⟩
  exact ⟨ModuleSheafTensor.pure _ _ ⊤ (divisorSection hI ⊤) s,
    divisorComplementFunction_cons hI m s⟩

/-- The original pole-function spaces form an increasing filtration. -/
theorem divisorPoleFunctions_mono : Monotone (divisorPoleFunctions hI) :=
  monotone_nat_of_le_succ (divisorPoleFunctions_le_succ hI)

/-- Products add pole bounds through the actual global section multiplication. -/
theorem divisorPoleFunctions_mul {m n : ℕ}
    {a b : Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤)}
    (ha : a ∈ divisorPoleFunctions hI m) (hb : b ∈ divisorPoleFunctions hI n) :
    a * b ∈ divisorPoleFunctions hI (m + n) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  exact ⟨SectionGradedMultiplication.mul _ ⊤ m n s t,
    divisorComplementFunction_mul hI m n s t⟩

/-- The constant one has every nonnegative pole bound. -/
theorem one_mem_divisorPoleFunctions (m : ℕ) :
    (1 : Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤)) ∈
      divisorPoleFunctions hI m :=
  ⟨tensorPowerSection _ ⊤ (divisorSection hI ⊤) m, divisorComplementFunction_power hI m⟩

/-- Powers of a represented function have the multiplied pole bound. -/
theorem divisorPoleFunctions_pow {m : ℕ}
    {a : Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤)}
    (ha : a ∈ divisorPoleFunctions hI m) (r : ℕ) :
    a ^ r ∈ divisorPoleFunctions hI (m * r) := by
  induction r with
  | zero => simpa only [pow_zero, Nat.mul_zero] using one_mem_divisorPoleFunctions hI 0
  | succ r ih =>
    simpa only [pow_succ, Nat.mul_succ] using divisorPoleFunctions_mul hI ih ha

end FLT.Mazur.FCurve
