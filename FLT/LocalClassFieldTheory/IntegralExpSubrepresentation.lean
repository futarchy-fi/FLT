/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralExpQuotient
public import FLT.LocalClassFieldTheory.IntegralUnitRepresentation
public import FLT.LocalClassFieldTheory.DiscreteOrderExact

/-!
# The exponential lattice inside the integral-unit representation

The actual integral-unit subgroup is Galois stable. Its inclusion into
field units identifies it with the constructed acyclic exponential subgroup.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

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

/-- The integral exponential subgroup as an integral submodule. -/
def integralExpSubmodule : Submodule ℤ (Additive Sˣ) :=
  (integralExpUnits R S K L p).toAddSubgroup.toIntSubmodule

/-- Every element of the field exponential subgroup comes from an integral unit. -/
theorem normalLatticeExpUnits_integral (u : normalLatticeExpUnits R S K L p) :
    ∃ s : Sˣ, Units.map (algebraMap S L).toMonoidHom s = u.val := by
  apply (discreteOrder_eq_one_iff S L u.val).mp
  obtain ⟨x, hx⟩ := u.property
  have hv : (dvrPrime S).valuation L (u.val : L) = 1 := by
    rw [← hx]
    exact adicLocalExp_valuation S L p _
      (scaledNormalLattice_mem_domain R S K L p (Multiplicative.toAdd x))
  simp [discreteOrder, hv]

/-- Integral inclusion identifies the two concrete versions of the exponential subgroup. -/
def integralExpToField : integralExpSubmodule R S K L p →ₗ[ℤ]
    Additive (normalLatticeExpUnits R S K L p) :=
  { toFun x := Additive.ofMul ⟨Units.map (algebraMap S L).toMonoidHom x.val.toMul, x.property⟩
    map_add' _ _ := by apply Subtype.ext; exact map_mul _ _ _
    map_smul' n x := by
      apply Subtype.ext
      exact map_zpow _ _ n }

/-- This comparison is bijective, using the proved integrality of every exponential. -/
theorem integralExpToField_bijective : Function.Bijective (integralExpToField R S K L p) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact Units.map_injective (IsFractionRing.injective S L) (congrArg Subtype.val h)
  · intro u
    obtain ⟨s, hs⟩ := normalLatticeExpUnits_integral R S K L p u.toMul
    refine ⟨⟨Additive.ofMul s, ?_⟩, ?_⟩
    · change Units.map (algebraMap S L).toMonoidHom s ∈ normalLatticeExpUnits R S K L p
      rw [hs]
      exact u.toMul.property
    · exact Subtype.ext hs

variable [IsIntegralClosure S R L]

/-- The natural integral Galois action preserves the exponential submodule. -/
theorem integralExpSubmodule_stable (g : Gal(L/K)) :
    integralExpSubmodule R S K L p ≤
      (integralExpSubmodule R S K L p).comap ((integralUnitRep R S K L).ρ g) := by
  intro u hu
  have h := normalLatticeExpUnits_galois R S K L p g
    ⟨Units.map (algebraMap S L).toMonoidHom u.toMul, hu⟩
  have he : Units.map (algebraMap S L).toMonoidHom
      (Units.map (galRestrict R K L S g).toMonoidHom u.toMul) =
      Units.map g.toMonoidHom (Units.map (algebraMap S L).toMonoidHom u.toMul) := by
    apply Units.ext
    exact algebraMap_galRestrictHom_apply R K L S g (u.toMul : S)
  change Units.map (algebraMap S L).toMonoidHom
    (Units.map (galRestrict R K L S g).toMonoidHom u.toMul) ∈
      normalLatticeExpUnits R S K L p
  rw [he]
  exact h

end LocalClassFieldTheory
