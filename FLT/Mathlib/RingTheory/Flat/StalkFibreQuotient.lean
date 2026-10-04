/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-! # The residue fibre of the map between local rings -/

@[expose] public noncomputable section

open scoped TensorProduct

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (P : Ideal S) [P.IsPrime]

/-- The fibre of the map on stalks is the quotient by the extension of the
original contracted prime. The equivalence is linear over the target stalk. -/
def stalkFibreQuotientEquiv :
    Localization.AtPrime P ⊗[Localization.AtPrime (P.comap (algebraMap R S))]
      (Localization.AtPrime (P.comap (algebraMap R S)) ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime (P.comap (algebraMap R S)))) ≃ₐ[
          Localization.AtPrime P]
    Localization.AtPrime P ⧸ (P.comap (algebraMap R S)).map
      (algebraMap R (Localization.AtPrime P)) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime P)
    (IsLocalRing.maximalIdeal (Localization.AtPrime (P.comap (algebraMap R S))))).symm.trans
      (Ideal.quotientEquivAlgOfEq _ (by
        rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (P.comap (algebraMap R S)),
          Ideal.map_map, ← IsScalarTower.algebraMap_eq]))

end Ideal
