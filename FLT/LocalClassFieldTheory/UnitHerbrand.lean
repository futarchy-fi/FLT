/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralExpSequence
public import FLT.LocalClassFieldTheory.FiniteCyclicHerbrand

/-!
# Herbrand quotient one for integral units

The constructed acyclic open subgroup identifies positive integral-unit
cohomology with that of a proved finite quotient. Cyclic finite-module
cardinal equality therefore gives Herbrand quotient one.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory Limits Rep.FiniteCyclicGroup

variable (R S K L : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [IsGalois K L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

variable [IsIntegralClosure S R L]

/-- The concrete quotient map induces an isomorphism in every positive degree. -/
theorem integralExpQuotient_cohomology_isIso (n : ℕ) :
    IsIso ((groupCohomology.functor ℤ Gal(L/K) (n + 1)).map
      (integralExpSequence R S K L p).g) := by
  let X := integralExpSequence R S K L p
  have hX := integralExpSequence_shortExact R S K L p
  have hz := integralExpRep_cohomology_isZero R S K L p n
  have hzs := integralExpRep_cohomology_isZero R S K L p (n + 1)
  let : Mono ((groupCohomology.functor ℤ Gal(L/K) (n + 1)).map X.g) :=
    ((groupCohomology.mapShortComplex₂ X (n + 1)).exact_iff_mono
      (IsZero.eq_zero_of_src hz _)).1 (groupCohomology.mapShortComplex₂_exact hX (n + 1))
  let : Epi ((groupCohomology.functor ℤ Gal(L/K) (n + 1)).map X.g) :=
    ((groupCohomology.mapShortComplex₃ hX (i := n + 1) rfl).exact_iff_epi
      (IsZero.eq_zero_of_tgt hzs _)).1 (groupCohomology.mapShortComplex₃_exact hX rfl)
  exact isIso_of_mono_of_epi _

/-- Positive integral-unit cohomology agrees with the actual finite quotient cohomology. -/
def integralUnitQuotientCohomologyIso (n : ℕ) :
    groupCohomology (integralUnitRep R S K L) (n + 1) ≅
      groupCohomology (integralExpQuotientRep R S K L p) (n + 1) :=
  @asIso (ModuleCat ℤ) _ _ _
    ((groupCohomology.functor ℤ Gal(L/K) (n + 1)).map (integralExpSequence R S K L p).g)
    (integralExpQuotient_cohomology_isIso R S K L p n)

variable [Finite (ResidueField S)] (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include p hg in
/-- The two positive periodic cohomology groups of integral units have equal order. -/
theorem integralUnit_H2_card_eq_H1 :
    Nat.card (groupCohomology (integralUnitRep R S K L) 2) =
      Nat.card (groupCohomology (integralUnitRep R S K L) 1) := by
  let : IsCyclic Gal(L/K) := ⟨⟨g, hg⟩⟩
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  let : Finite (integralExpQuotientRep R S K L p).V :=
    integralExpQuotientRep_finite R S K L p
  calc
    _ = Nat.card (groupCohomology (integralExpQuotientRep R S K L p) 2) :=
      Nat.card_congr (integralUnitQuotientCohomologyIso R S K L p 1).toLinearEquiv.toEquiv
    _ = Nat.card (groupCohomology (integralExpQuotientRep R S K L p) 1) :=
      finiteCyclic_H2_card_eq_H1 _ g hg
    _ = _ := Nat.card_congr
      (integralUnitQuotientCohomologyIso R S K L p 0).toLinearEquiv.toEquiv.symm

include p hg in
/-- Integral-unit H¹ is finite, using the actual quotient rather than an assumed order. -/
theorem integralUnit_H1_finite : Finite (groupCohomology (integralUnitRep R S K L) 1) := by
  let : IsCyclic Gal(L/K) := ⟨⟨g, hg⟩⟩
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  let : Finite (integralExpQuotientRep R S K L p).V :=
    integralExpQuotientRep_finite R S K L p
  let := finiteCyclic_odd_finite (integralExpQuotientRep R S K L p) g hg 1 (by decide)
  exact Finite.of_equiv _
    (integralUnitQuotientCohomologyIso R S K L p 0).toLinearEquiv.toEquiv.symm

include p hg in
/-- The Herbrand quotient of the integral units of a cyclic local extension is one. -/
theorem integralUnit_herbrand_eq_one :
    (Nat.card (groupCohomology (integralUnitRep R S K L) 2) : ℚ) /
      Nat.card (groupCohomology (integralUnitRep R S K L) 1) = 1 := by
  let := integralUnit_H1_finite R S K L p g hg
  rw [integralUnit_H2_card_eq_H1 R S K L p g hg]
  exact div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end LocalClassFieldTheory
