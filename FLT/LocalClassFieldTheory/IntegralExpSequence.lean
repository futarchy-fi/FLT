/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralExpSubrepresentation
public import FLT.LocalClassFieldTheory.UnramifiedOrderSequence

/-!
# The exponential integral-unit short exact sequence

Use the actual invariant submodule and its quotient representation.
Prove short exactness and transfer the exponential subgroup's acyclicity.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory Limits

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

/-- The natural subrepresentation on the integral exponential subgroup. -/
abbrev integralExpRep : Rep ℤ Gal(L/K) :=
  (integralUnitRep R S K L).subrepresentation (integralExpSubmodule R S K L p)
    (integralExpSubmodule_stable R S K L p)

/-- The actual quotient representation of integral units by the exponential subgroup. -/
abbrev integralExpQuotientRep : Rep ℤ Gal(L/K) :=
  (integralUnitRep R S K L).quotient (integralExpSubmodule R S K L p)
    (integralExpSubmodule_stable R S K L p)

/-- The inclusion and quotient maps form a short complex. -/
def integralExpSequence : ShortComplex (Rep ℤ Gal(L/K)) :=
  ShortComplex.mk
    ((integralUnitRep R S K L).subtype (integralExpSubmodule R S K L p)
      (integralExpSubmodule_stable R S K L p))
    ((integralUnitRep R S K L).mkQ (integralExpSubmodule R S K L p)
      (integralExpSubmodule_stable R S K L p)) (by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        exact (Submodule.Quotient.mk_eq_zero _).mpr x.property)

/-- Exactness follows from the subgroup inclusion and the concrete quotient map. -/
theorem integralExpSequence_shortExact : (integralExpSequence R S K L p).ShortExact where
  mono_f := (Rep.mono_iff_injective _).mpr Subtype.val_injective
  epi_g := (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  exact := by
    apply representation_exact_of_functions
    intro x hx
    exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero _).mp hx⟩, rfl⟩

/-- The underlying finite quotient proved topologically is the coefficient quotient here. -/
theorem integralExpQuotientRep_finite [Finite (ResidueField S)] :
    Finite (integralExpQuotientRep R S K L p).V :=
  integralExpUnits_quotient_finite R S K L p

/-- Integral inclusion intertwines the actual and transported exponential actions. -/
theorem integralExpToField_action (g : Gal(L/K)) (x : integralExpSubmodule R S K L p) :
    integralExpToField R S K L p ((integralExpRep R S K L p).ρ g x) =
      normalLatticeExpRepresentation R S K L p g (integralExpToField R S K L p x) := by
  apply Subtype.ext
  change _ = (Additive.toMul (normalLatticeExpRepresentation R S K L p g
    (integralExpToField R S K L p x))).val
  rw [normalLatticeExpRepresentation_action]
  apply Units.ext
  exact algebraMap_galRestrictHom_apply R K L S g (x.val.toMul : S)

/-- Cohomology agrees with the proved acyclic exponential representation. -/
def integralExpCohomologyIso (i : ℕ) :
    groupCohomology (integralExpRep R S K L p) i ≅
      groupCohomology (Rep.of (normalLatticeExpRepresentation R S K L p)) i :=
  groupCohomology.mapIso (MulEquiv.refl Gal(L/K))
    (LinearEquiv.ofBijective _ (integralExpToField_bijective R S K L p))
    (fun g => by
      apply LinearMap.ext
      exact integralExpToField_action R S K L p g) i

/-- Every positive cohomology group of the actual integral exponential subgroup is zero. -/
theorem integralExpRep_cohomology_isZero (i : ℕ) :
    IsZero (groupCohomology (integralExpRep R S K L p) (i + 1)) :=
  (normalLatticeExpUnits_cohomology_isZero R S K L p i).of_iso
    (integralExpCohomologyIso R S K L p (i + 1))

end LocalClassFieldTheory
