/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicLogTransport

/-! # Actual de Rham logarithms of arbitrary tilt elements with sharp equal to one -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Finset
variable (p : ℕ) [Fact p.Prime]

/-- The Teichmuller difference of the specified tilt element in the original period ring. -/
def complexTiltLogArgument (z : IntegralTilt p) : ComplexBDeRhamPlus p :=
  algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p)
    (algebraMap (Ainf p) (ComplexAinfInvertP p) (WittVector.teichmuller p z - 1))

/-- Sharp equal to one puts the actual Teichmuller difference in the theta ideal. -/
theorem complexTiltLogArgument_mem (z : IntegralTilt p) (hz : complexSharp p z = 1) :
    complexTiltLogArgument p z ∈ Ideal.span {complexDeRhamParameter p} := by
  rw [← complexDeRhamTheta_ker]
  change complexDeRhamTheta p (complexTiltLogArgument p z) = 0
  rw [complexTiltLogArgument, complexDeRhamTheta_algebraMap, map_sub,
    complexTheta_teichmuller, hz, map_one, sub_self]
  rfl

/-- Successive powers make the actual logarithm converge adically. -/
theorem complexTiltLog_term_mem (z : IntegralTilt p) (hz : complexSharp p z = 1) (n : ℕ) :
    complexLogCoefficient p n * complexTiltLogArgument p z ^ n ∈
      Ideal.span {complexDeRhamParameter p} ^ n :=
  Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (complexTiltLogArgument_mem p z hz) n)

/-- The logarithmic period attached to this specific sharp-one tilt element. -/
def complexTiltLog (z : IntegralTilt p) (hz : complexSharp p z = 1) : ComplexBDeRhamPlus p :=
  adicSeries (Ideal.span {complexDeRhamParameter p})
    (fun n ↦ complexLogCoefficient p n * complexTiltLogArgument p z ^ n)
    (complexTiltLog_term_mem p z hz)

/-- Every finite approximation is determined by the original tilt element. -/
theorem complexTiltLog_truncation (z : IntegralTilt p) (hz : complexSharp p z = 1) (n : ℕ) :
    complexTiltLog p z hz ≡
      (∑ k ∈ range n, complexLogCoefficient p k * complexTiltLogArgument p z ^ k)
        [SMOD ((Ideal.span {complexDeRhamParameter p}) ^ n • ⊤ : Ideal (ComplexBDeRhamPlus p))] :=
  (adicSeries_spec _ _ _ n).symm

/-- The actual period belongs to the first de Rham filtration step. -/
theorem complexTiltLog_mem (z : IntegralTilt p) (hz : complexSharp p z = 1) :
    complexTiltLog p z hz ∈ Ideal.span {complexDeRhamParameter p} := by
  have h := complexTiltLog_truncation p z hz 1
  rw [SModEq.sub_mem] at h
  simpa [complexLogCoefficient] using h

/-- Its first infinitesimal term is the specified Teichmuller difference. -/
theorem complexTiltLog_sub_argument_mem (z : IntegralTilt p) (hz : complexSharp p z = 1) :
    complexTiltLog p z hz - complexTiltLogArgument p z ∈
      Ideal.span {complexDeRhamParameter p} ^ 2 := by
  have h := complexTiltLog_truncation p z hz 2
  rw [SModEq.sub_mem] at h
  simpa [sum_range_succ, complexLogCoefficient, Ring.inverse_one] using h

/-- The argument is transported by the existing original period-ring action. -/
theorem complexTiltLogArgument_galois (σ : PadicGalois p) (z : IntegralTilt p) :
    complexDeRhamGalois p σ (complexTiltLogArgument p z) =
      complexTiltLogArgument p (complexTiltGalois p σ z) := by
  rw [complexTiltLogArgument, complexDeRhamGalois_algebraMap,
    complexLocalizedGalois_algebraMap]
  congr 2
  simp [complexAinfGalois]

/-- Galois transport commutes with the actual convergent logarithm. -/
theorem complexTiltLog_galois (σ : PadicGalois p) (z : IntegralTilt p)
    (hz : complexSharp p z = 1) :
    complexDeRhamGalois p σ (complexTiltLog p z hz) =
      complexTiltLog p (complexTiltGalois p σ z)
        (by rw [complexSharp_equivariant, hz, map_one]) := by
  unfold complexTiltLog
  rw [adicSeries_map _ _ (complexDeRhamGalois_ideal p σ)]
  simp only [map_mul, map_pow, complexLogCoefficient_galois, complexTiltLogArgument_galois]

end PadicHodgeTheory
