/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexLocalizedScalars
public import FLT.PadicHodgeTheory.DividedPowerHull
public import Mathlib.RingTheory.DividedPowers.RatAlgebra

/-!
# A divided-power hull for the family's actual theta ideal

Construct the least subring of A_inf[1/p] containing A_inf and closed under
the rational divided powers on the theta ideal. It carries actual divided
powers and a map to the family's B_dR^+. Identification with an abstract PD
envelope, p-adic completion, and Frobenius stability remain separate steps.
-/

@[expose] public noncomputable section
open scoped PadicHodgeTheory
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Rational divided powers on the actual localized theta ideal. -/
def complexLocalizedThetaDividedPowers : DividedPowers (ComplexDeRhamIdeal p) := by
  classical
  exact DividedPowers.RatAlgebra.dividedPowers _

/-- The embedded divided-power hull of A_inf in its localization. -/
def complexAinfPDHullSubring : Subring (ComplexAinfInvertP p) :=
  (complexLocalizedThetaDividedPowers p).hull
    (algebraMap (Ainf p) (ComplexAinfInvertP p)).range

/-- The underlying ring of the constructed hull. -/
abbrev ComplexAinfPDHull := complexAinfPDHullSubring p

/-- The integral Witt ring maps to the hull by its original localization map. -/
def complexAinfToPDHull : Ainf p →+* ComplexAinfPDHull p :=
  (algebraMap (Ainf p) (ComplexAinfInvertP p)).codRestrict _ (fun x ↦
    (complexLocalizedThetaDividedPowers p).le_hull _ ⟨x, rfl⟩)

/-- The theta ideal inside the hull. -/
def complexPDHullIdeal : Ideal (ComplexAinfPDHull p) :=
  (complexLocalizedThetaDividedPowers p).hullIdeal _

/-- Actual divided powers on the constructed theta ideal, without a PD hypothesis. -/
def complexPDHullDividedPowers : DividedPowers (complexPDHullIdeal p) :=
  (complexLocalizedThetaDividedPowers p).hullDividedPowers _

/-- The original theta generator belongs to the constructed divided-power ideal. -/
theorem complexPDHull_generator_mem :
    complexAinfToPDHull p (complexThetaGenerator p) ∈ complexPDHullIdeal p := by
  change algebraMap (Ainf p) (ComplexAinfInvertP p) (complexThetaGenerator p) ∈
    RingHom.ker (complexThetaInvertP p)
  rw [complexThetaInvertP_ker_eq_span]
  exact Ideal.subset_span rfl

/-- The divided powers of xi are elements of this integral hull. -/
def complexPDHullGeneratorDpow (n : ℕ) : ComplexAinfPDHull p :=
  (complexPDHullDividedPowers p).dpow n (complexAinfToPDHull p (complexThetaGenerator p))

/-- They satisfy the factorial denominator equation in the hull itself. -/
theorem complexPDHullGeneratorDpow_factorial (n : ℕ) :
    (n.factorial : ComplexAinfPDHull p) * complexPDHullGeneratorDpow p n =
      complexAinfToPDHull p (complexThetaGenerator p) ^ n :=
  (complexPDHullDividedPowers p).factorial_mul_dpow_eq_pow (complexPDHull_generator_mem p)

/-- The hull maps to the existing de Rham completion. -/
def complexPDHullToDeRham : ComplexAinfPDHull p →+* ComplexBDeRhamPlus p :=
  (algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p)).comp
    (complexAinfPDHullSubring p).subtype

/-- This comparison retains the family's original map from A_inf. -/
theorem complexPDHullToDeRham_integral (x : Ainf p) :
    complexPDHullToDeRham p (complexAinfToPDHull p x) = complexAinfToDeRham p x := rfl

/-- The divided powers are the actual rational factorial expressions in A_inf[1/p]. -/
theorem complexPDHullGeneratorDpow_coe (n : ℕ) :
    (complexPDHullGeneratorDpow p n : ComplexAinfInvertP p) =
      Ring.inverse (n.factorial : ComplexAinfInvertP p) *
        algebraMap (Ainf p) (ComplexAinfInvertP p) (complexThetaGenerator p) ^ n := by
  classical
  change (complexLocalizedThetaDividedPowers p).dpow n _ = _
  exact DividedPowers.RatAlgebra.dpow_eq_of_mem n (complexPDHull_generator_mem p)

end PadicHodgeTheory
