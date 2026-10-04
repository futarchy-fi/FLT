/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexAinfFrobenius
public import FLT.PadicHodgeTheory.ComplexLocalizedGalois

/-!
# Frobenius after inverting p in the family's A_inf

Frobenius extends through localization and commutes with Galois. No positive
power of the de Rham ideal is carried into that ideal, so completing directly
at theta does not supply the crystalline Frobenius construction.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Frobenius on the family's actual localization A_inf[1/p]. -/
def complexLocalizedFrobenius : ComplexAinfInvertP p →+* ComplexAinfInvertP p :=
  IsLocalization.map (M := Submonoid.powers (p : Ainf p))
    (T := Submonoid.powers (p : Ainf p)) _ (complexAinfFrobenius p).toRingHom (by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers, map_natCast])

/-- The localized map extends the integral Frobenius. -/
@[simp] theorem complexLocalizedFrobenius_algebraMap (x : Ainf p) :
    complexLocalizedFrobenius p (algebraMap (Ainf p) (ComplexAinfInvertP p) x) =
      algebraMap (Ainf p) (ComplexAinfInvertP p) (complexAinfFrobenius p x) :=
  IsLocalization.map_eq _ _

/-- Frobenius commutes with Galois on the localization as well. -/
theorem complexLocalizedFrobenius_galois (σ : PadicGalois p) (x : ComplexAinfInvertP p) :
    complexLocalizedFrobenius p (complexLocalizedGalois p σ x) =
      complexLocalizedGalois p σ (complexLocalizedFrobenius p x) := by
  suffices h : (complexLocalizedFrobenius p).comp (complexLocalizedGalois p σ) =
      (complexLocalizedGalois p σ).comp (complexLocalizedFrobenius p) from
    DFunLike.congr_fun h x
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p))
  ext y
  simp only [RingHom.comp_apply, complexLocalizedFrobenius_algebraMap,
    complexLocalizedGalois_algebraMap, complexAinfFrobenius_galois]

/-- The obstruction remains nonzero after localizing and identifying theta's target with C_p. -/
theorem complexLocalizedTheta_frobenius_generator_ne_zero :
    complexLocalizedTheta p (complexLocalizedFrobenius p
      (algebraMap (Ainf p) (ComplexAinfInvertP p) (complexThetaGenerator p))) ≠ 0 := by
  rw [complexLocalizedFrobenius_algebraMap, complexLocalizedTheta_algebraMap]
  exact fun h ↦ complexTheta_frobenius_generator_ne_zero p (Subtype.ext h)

/-- Even arbitrarily high powers of the completion ideal fail to map into it. -/
theorem complexLocalizedFrobenius_no_ideal_power (n : ℕ) :
    ¬ ComplexDeRhamIdeal p ^ n ≤
      (ComplexDeRhamIdeal p).comap (complexLocalizedFrobenius p) := by
  intro h
  let x := algebraMap (Ainf p) (ComplexAinfInvertP p) (complexThetaGenerator p)
  have hx : x ∈ ComplexDeRhamIdeal p := by
    rw [← complexLocalizedTheta_ker]
    change complexLocalizedTheta p x = 0
    simp only [x, complexLocalizedTheta_algebraMap,
      show complexTheta p (complexThetaGenerator p) = 0 from complexThetaGenerator_mem_ker p,
      ZeroMemClass.coe_zero]
  have hz := h (Ideal.pow_mem_pow hx n)
  rw [← complexLocalizedTheta_ker] at hz
  change complexLocalizedTheta p (complexLocalizedFrobenius p (x ^ n)) = 0 at hz
  rw [map_pow, map_pow] at hz
  exact pow_ne_zero n (complexLocalizedTheta_frobenius_generator_ne_zero p) hz

end PadicHodgeTheory
