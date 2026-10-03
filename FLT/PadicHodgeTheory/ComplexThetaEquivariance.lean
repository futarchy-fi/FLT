/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexSharpEquivariance
public import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-! # Equivariance of Fontaine theta on the actual A_inf -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The Galois action on Fontaine's Witt vectors is induced coefficientwise. -/
def complexAinfGalois (σ : PadicGalois p) : Ainf p →+* Ainf p :=
  WittVector.map (complexTiltGalois p σ)

/-- The zeroth and higher Witt coefficients retain the tilt action. -/
@[simp] theorem complexAinfGalois_coeff (σ : PadicGalois p) (x : Ainf p) (n : ℕ) :
    (complexAinfGalois p σ x).coeff n = complexTiltGalois p σ (x.coeff n) := rfl

/-- The Witt action respects identity. -/
@[simp] theorem complexAinfGalois_one (x : Ainf p) : complexAinfGalois p 1 x = x := by
  ext n
  exact complexTiltGalois_one p _

/-- The Witt action respects composition. -/
theorem complexAinfGalois_mul (σ τ : PadicGalois p) (x : Ainf p) :
    complexAinfGalois p (σ * τ) x = complexAinfGalois p σ (complexAinfGalois p τ x) := by
  ext n
  exact complexTiltGalois_mul p σ τ _

/-- Fontaine's actual Witt ring carries the induced Galois action. -/
instance instMulSemiringActionAinf : MulSemiringAction (PadicGalois p) (Ainf p) where
  smul σ x := complexAinfGalois p σ x
  one_smul := complexAinfGalois_one p
  mul_smul := complexAinfGalois_mul p
  smul_zero σ := map_zero (complexAinfGalois p σ)
  smul_add σ := map_add (complexAinfGalois p σ)
  smul_one σ := map_one (complexAinfGalois p σ)
  smul_mul σ := map_mul (complexAinfGalois p σ)

/-- Theta commutes with Galois on every Teichmuller representative. -/
theorem complexTheta_equivariant_teichmuller (σ : PadicGalois p) (x : IntegralTilt p) :
    complexTheta p (complexAinfGalois p σ (WittVector.teichmuller p x)) =
      complexIntegerGalois p σ (complexTheta p (WittVector.teichmuller p x)) := by
  simp only [complexAinfGalois, WittVector.map_teichmuller,
    complexTheta_teichmuller, complexSharp_equivariant]

/-- Equality modulo every power of p promotes Teichmuller equivariance to all A_inf. -/
theorem complexTheta_equivariant (σ : PadicGalois p) (x : Ainf p) :
    complexTheta p (complexAinfGalois p σ x) =
      complexIntegerGalois p σ (complexTheta p x) := by
  let I : Ideal 𝓞_ℂ_[p] := Ideal.span {(p : 𝓞_ℂ_[p])}
  suffices h : (fun y ↦ complexTheta p (complexAinfGalois p σ y)) =
      (fun y ↦ complexIntegerGalois p σ (complexTheta p y)) from congrFun h x
  apply IsHausdorff.funext' I
  intro n y
  have hp : IsNilpotent (p : 𝓞_ℂ_[p] ⧸ I ^ n) := by
    refine ⟨n, ?_⟩
    rw [← map_natCast (Ideal.Quotient.mk (I ^ n)), ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n
  exact congrArg (fun f : Ainf p →+* 𝓞_ℂ_[p] ⧸ I ^ n ↦ f y)
    (WittVector.eq_of_apply_teichmuller_eq
      ((Ideal.Quotient.mk (I ^ n)).comp ((complexTheta p).comp (complexAinfGalois p σ)))
      ((Ideal.Quotient.mk (I ^ n)).comp ((complexIntegerGalois p σ).comp (complexTheta p)))
      hp (fun z ↦ congrArg (Ideal.Quotient.mk (I ^ n))
        (complexTheta_equivariant_teichmuller p σ z)))

/-- In particular the actual theta kernel is Galois stable. -/
theorem complexTheta_ker_stable (σ : PadicGalois p) (x : Ainf p)
    (hx : x ∈ RingHom.ker (complexTheta p)) :
    complexAinfGalois p σ x ∈ RingHom.ker (complexTheta p) := by
  change complexTheta p (complexAinfGalois p σ x) = 0
  rw [complexTheta_equivariant, show complexTheta p x = 0 from hx, map_zero]

end PadicHodgeTheory
