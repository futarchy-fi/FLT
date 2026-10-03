/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexPadicScalars

/-! # The actual Galois action fixes the p-adic scalar embeddings -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Galois fixes the prime-field Witt scalars before localization. -/
theorem complexPadicIntToAinf_galois (σ : PadicGalois p) (x : ℤ_[p]) :
    complexAinfGalois p σ (complexPadicIntToAinf p x) = complexPadicIntToAinf p x := by
  have h : (complexTiltGalois p σ).comp (ZMod.castHom (dvd_refl p) (IntegralTilt p)) =
      ZMod.castHom (dvd_refl p) (IntegralTilt p) := Subsingleton.elim _ _
  ext n
  exact RingHom.congr_fun h (((WittVector.equiv p).symm x).coeff n)

/-- The completed action fixes every integral p-adic scalar. -/
@[simp] theorem complexPadicIntToDeRham_galois (σ : PadicGalois p) (x : ℤ_[p]) :
    complexDeRhamGalois p σ (complexPadicIntToDeRham p x) = complexPadicIntToDeRham p x := by
  change complexDeRhamGalois p σ
    (algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p)
      (algebraMap (Ainf p) (ComplexAinfInvertP p) (complexPadicIntToAinf p x))) = _
  rw [complexDeRhamGalois_algebraMap, complexLocalizedGalois_algebraMap,
    complexPadicIntToAinf_galois]
  rfl

/-- The completed action fixes every scalar in the actual p-adic field. -/
@[simp] theorem complexPadicToDeRham_galois (σ : PadicGalois p) (x : ℚ_[p]) :
    complexDeRhamGalois p σ (complexPadicToDeRham p x) = complexPadicToDeRham p x := by
  have h : (complexDeRhamGalois p σ).comp (complexPadicToDeRham p) =
      complexPadicToDeRham p := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    ext y
    simp only [RingHom.comp_apply, complexPadicToDeRham_int, complexPadicIntToDeRham_galois]
  exact RingHom.congr_fun h x

end PadicHodgeTheory
