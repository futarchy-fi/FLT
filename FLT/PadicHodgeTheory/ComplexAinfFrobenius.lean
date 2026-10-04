/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexThetaEquivariance
public import FLT.PadicHodgeTheory.ComplexThetaGenerator
public import FLT.PadicHodgeTheory.ComplexPadicScalars

/-!
# Frobenius on the family's actual A_inf

The Witt Frobenius commutes with Galois and fixes the constructed p-adic
scalars. Its effect on the theta generator explains why a crystalline
construction requires more than descent through the theta quotient.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Witt Frobenius on the actual perfect integral tilt. -/
def complexAinfFrobenius : Ainf p ≃+* Ainf p :=
  WittVector.frobeniusEquiv p (IntegralTilt p)

/-- Frobenius raises each tilt coefficient to its p-th power. -/
theorem complexAinfFrobenius_coeff (x : Ainf p) (n : ℕ) :
    (complexAinfFrobenius p x).coeff n = x.coeff n ^ p :=
  WittVector.coeff_frobenius_charP p x n

/-- Frobenius commutes with the existing Galois action. -/
theorem complexAinfFrobenius_galois (σ : PadicGalois p) (x : Ainf p) :
    complexAinfFrobenius p (complexAinfGalois p σ x) =
      complexAinfGalois p σ (complexAinfFrobenius p x) := by
  ext n
  simp only [complexAinfFrobenius_coeff, complexAinfGalois_coeff, map_pow]

/-- On Teichmuller elements it agrees with the multiplicative p-th power. -/
theorem complexAinfFrobenius_teichmuller (x : IntegralTilt p) :
    complexAinfFrobenius p (WittVector.teichmuller p x) =
      WittVector.teichmuller p (x ^ p) := by
  change WittVector.frobenius _ = _
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller]
  rfl

/-- The existing integral p-adic scalar embedding is pointwise fixed. -/
theorem complexAinfFrobenius_padic (x : ℤ_[p]) :
    complexAinfFrobenius p (complexPadicIntToAinf p x) = complexPadicIntToAinf p x := by
  ext n
  rw [complexAinfFrobenius_coeff]
  change (ZMod.castHom (dvd_refl p) (IntegralTilt p)) _ ^ p = _
  rw [← map_pow, ZMod.pow_card]
  rfl

/-- The actual theta generator is not sent to another theta-kernel element. -/
theorem complexTheta_frobenius_generator :
    complexTheta p (complexAinfFrobenius p (complexThetaGenerator p)) =
      (p : 𝓞_ℂ_[p]) ^ p - p := by
  simp only [complexThetaGenerator, map_sub, map_natCast,
    complexAinfFrobenius_teichmuller, complexTheta_teichmuller, map_pow,
    complexPrimeTilt_sharp]

/-- The obstruction is nonzero for every prime, including two. -/
theorem complexTheta_frobenius_generator_ne_zero :
    complexTheta p (complexAinfFrobenius p (complexThetaGenerator p)) ≠ 0 := by
  rw [complexTheta_frobenius_generator, sub_ne_zero]
  have hp : p < p ^ p := by
    simpa only [pow_one] using
      (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Fact.out : p.Prime).one_lt)
  exact_mod_cast hp.ne'

/-- Frobenius does not preserve the kernel of the family's theta map. -/
theorem complexAinfFrobenius_not_preserves_theta :
    ¬ RingHom.ker (complexTheta p) ≤
      (RingHom.ker (complexTheta p)).comap (complexAinfFrobenius p).toRingHom := by
  intro h
  exact complexTheta_frobenius_generator_ne_zero p (h (complexThetaGenerator_mem_ker p))

/-- There is no ring endomorphism of O_C induced by this Frobenius through theta. -/
theorem complexAinfFrobenius_no_theta_descent :
    ¬ ∃ f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p],
      f.comp (complexTheta p) = (complexTheta p).comp (complexAinfFrobenius p).toRingHom := by
  rintro ⟨f, hf⟩
  have h := DFunLike.congr_fun hf (complexThetaGenerator p)
  have hz : complexTheta p (complexThetaGenerator p) = 0 := complexThetaGenerator_mem_ker p
  simp only [RingHom.comp_apply, hz, map_zero] at h
  exact complexTheta_frobenius_generator_ne_zero p h.symm

end PadicHodgeTheory
