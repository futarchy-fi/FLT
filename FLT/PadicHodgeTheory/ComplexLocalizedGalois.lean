/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexThetaEquivariance
public import FLT.PadicHodgeTheory.ComplexDeRhamResidue

/-! # Galois action after inverting p in the actual Witt ring -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Extend the actual Witt action through inversion of p. -/
def complexLocalizedGalois (σ : PadicGalois p) :
    ComplexAinfInvertP p →+* ComplexAinfInvertP p :=
  IsLocalization.map (M := Submonoid.powers (p : Ainf p))
    (T := Submonoid.powers (p : Ainf p)) _ (complexAinfGalois p σ) (by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers, map_natCast])

/-- The localized action retains the actual Witt action. -/
@[simp] theorem complexLocalizedGalois_algebraMap (σ : PadicGalois p) (x : Ainf p) :
    complexLocalizedGalois p σ (algebraMap (Ainf p) (ComplexAinfInvertP p) x) =
      algebraMap (Ainf p) (ComplexAinfInvertP p) (complexAinfGalois p σ x) :=
  IsLocalization.map_eq _ _

/-- Localization preserves the identity action. -/
@[simp] theorem complexLocalizedGalois_one : complexLocalizedGalois p 1 = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p))
  ext x
  simp

/-- Localization preserves composition of the actual automorphisms. -/
theorem complexLocalizedGalois_mul (σ τ : PadicGalois p) :
    complexLocalizedGalois p (σ * τ) =
      (complexLocalizedGalois p σ).comp (complexLocalizedGalois p τ) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p))
  ext x
  simp [complexAinfGalois_mul]

/-- Localized theta with its target identified with the actual C_p. -/
def complexLocalizedTheta : ComplexAinfInvertP p →+* ℂ_[p] :=
  (complexIntegerInvertPEquiv p).toRingHom.comp (complexThetaInvertP p)

/-- On Witt vectors this is the original integral theta. -/
@[simp] theorem complexLocalizedTheta_algebraMap (x : Ainf p) :
    complexLocalizedTheta p (algebraMap (Ainf p) (ComplexAinfInvertP p) x) =
      (complexTheta p x : ℂ_[p]) := by
  simp [complexLocalizedTheta, complexThetaInvertP_algebraMap]

/-- The actual localized theta intertwines both Galois actions. -/
theorem complexLocalizedTheta_equivariant (σ : PadicGalois p) (x : ComplexAinfInvertP p) :
    complexLocalizedTheta p (complexLocalizedGalois p σ x) =
      complexGalois p σ (complexLocalizedTheta p x) := by
  suffices h : (complexLocalizedTheta p).comp (complexLocalizedGalois p σ) =
      (complexGalois p σ).comp (complexLocalizedTheta p) from DFunLike.congr_fun h x
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p))
  ext y
  simp only [RingHom.comp_apply, complexLocalizedGalois_algebraMap,
    complexLocalizedTheta_algebraMap, complexTheta_equivariant]
  rfl

/-- Identifying the target does not change the ideal defining the completion. -/
theorem complexLocalizedTheta_ker : RingHom.ker (complexLocalizedTheta p) =
    ComplexDeRhamIdeal p := by
  ext x
  exact map_eq_zero_iff (complexIntegerInvertPEquiv p) (complexIntegerInvertPEquiv p).injective

/-- Each Galois endomorphism preserves the actual completion ideal. -/
theorem complexLocalizedGalois_ideal (σ : PadicGalois p) :
    ComplexDeRhamIdeal p ≤ (ComplexDeRhamIdeal p).comap (complexLocalizedGalois p σ) := by
  rw [← complexLocalizedTheta_ker]
  intro x hx
  change complexLocalizedTheta p (complexLocalizedGalois p σ x) = 0
  rw [complexLocalizedTheta_equivariant, show complexLocalizedTheta p x = 0 from hx, map_zero]

end PadicHodgeTheory
