/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalFiberRegularQuotient
public import FLT.Mazur.PrimeCoefficientLocalization
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Applying the local criterion at an ambient prime

Localizing a flat map at an ambient prime and its contraction constructs the
flat local homomorphism required by the closed-fiber criterion. Its principal
quotient is flat over the original base, not just over the localized base.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.PrimeLocalFiberRegularQuotient
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
  [IsNoetherianRing R] [IsNoetherianRing B] [Module.Flat R B]

/-- The localized equation is regular and its full quotient is flat over the original base. -/
theorem regular_and_flat (q : Ideal B) [q.IsPrime] (a : B)
    (ha : let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
      IsRegular (1 ⊗ₜ[Localization.AtPrime (q.under R)]
        algebraMap B (Localization.AtPrime q) a :
          IsLocalRing.ResidueField (Localization.AtPrime (q.under R))
            ⊗[Localization.AtPrime (q.under R)] Localization.AtPrime q)) :
    IsRegular (algebraMap B (Localization.AtPrime q) a) ∧
      Module.Flat R (Localization.AtPrime q ⧸
        Ideal.span {algebraMap B (Localization.AtPrime q) a}) := by
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  let _ := FCurve.primeCoefficient_localHom (q.under R) q
  let _ : Module.Flat (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R))
      (q.under R).primeCompl (Localization.AtPrime q)).mpr inferInstance
  have hr := LocalFiberRegularQuotient.regular _ ha
  let _ := LocalFiberRegularQuotient.quotient_flat _ ha
  exact ⟨hr, Module.Flat.trans R (Localization.AtPrime (q.under R)) _⟩

end FLT.Mazur.PrimeLocalFiberRegularQuotient
