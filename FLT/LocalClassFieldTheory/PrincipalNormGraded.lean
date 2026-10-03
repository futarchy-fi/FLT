/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PrincipalNormCorrection

/-!
# The norm on the actual graded quotients

The quotient map induced by norm is conjugate to the additive residue trace
under the principal-unit residue identifications.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

/-- The n-th graded principal-unit group. -/
abbrev PrincipalGraded {R : Type*} [CommRing R] (π : R) (n : ℕ) :=
  principalUnits π n ⧸ (principalUnits π (n + 1)).comap (principalUnits π n).subtype

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  {π : R} (hπ : Irreducible π)

/-- Norm descends to the quotients of successive principal-unit subgroups. -/
def principalNormGraded (π : R) (n : ℕ) :
    PrincipalGraded (algebraMap R S π) n →* PrincipalGraded π n :=
  QuotientGroup.map _ _ (principalNorm R S π n) (by
    intro u hu
    change (principalNorm R S π n u).val ∈ principalUnits π (n + 1)
    exact (principalNorm R S π (n + 1) ⟨u.val, hu⟩).property)

/-- The quotient norm is the residue-field trace in divided-coefficient coordinates. -/
theorem principalNormGraded_trace (n : ℕ) (hn : 0 < n)
    (q : PrincipalGraded (algebraMap R S π) n) :
    Multiplicative.toAdd
      (principalUnitsQuotientEquiv hπ.ne_zero hπ.not_isUnit n hn hπ.maximalIdeal_eq
        (principalNormGraded R S π n q)) =
      Algebra.trace (ResidueField R) (ResidueField S)
        (Multiplicative.toAdd (principalUnitsQuotientEquiv
          (unramified_uniformizer_ne_zero R S hπ)
          (unramified_uniformizer_irreducible R S hπ).not_isUnit n hn
          (unramified_maximalIdeal_eq R S hπ) q)) := by
  induction q using QuotientGroup.induction_on with
  | H u => exact principalNorm_residue R S hπ.ne_zero hπ.not_isUnit n hn u

include hπ in
/-- In particular, the induced norm is surjective at every positive level. -/
theorem principalNormGraded_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (principalNormGraded R S π n) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H u =>
    obtain ⟨v, hv⟩ := exists_principalNorm_symbol R S hπ n hn u
    refine ⟨QuotientGroup.mk v, ?_⟩
    apply (principalUnitsQuotientEquiv hπ.ne_zero hπ.not_isUnit n hn
      hπ.maximalIdeal_eq).injective
    exact congrArg Multiplicative.ofAdd hv

end LocalClassFieldTheory
