/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexFiniteLogLimit

/-! # The actual cyclotomic logarithm transforms by the cyclotomic character -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Separatedness of the actual theta inverse limit gives sigma(t) = chi(sigma)t. -/
theorem complexCyclotomicLog_galois_character (σ : PadicGalois p) :
    complexDeRhamGalois p σ (complexCyclotomicLog p) =
      complexPadicToDeRham p
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) *
          complexCyclotomicLog p := by
  apply AdicCompletion.ext_evalₐ
  intro r
  change complexDeRhamFiniteEval p r
    (complexDeRhamGalois p σ (complexCyclotomicLog p)) =
      complexDeRhamFiniteEval p r (_ * _)
  rw [map_mul, complexCyclotomicLog_character_finite]
  congr 1
  exact (complexFiniteThetaQuotientScalars_eval p r _).symm

/-- The semiring action on the constructed period has the same scalar formula. -/
theorem complexCyclotomicLog_smul_character (σ : PadicGalois p) :
    σ • complexCyclotomicLog p =
      complexPadicToDeRham p
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) *
          complexCyclotomicLog p :=
  complexCyclotomicLog_galois_character p σ

end PadicHodgeTheory
