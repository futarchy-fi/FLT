/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedUnitHilbert90
public import Mathlib.RingTheory.Invariant.Galois

/-!
# The Galois representation on integral units

The action is the actual restriction of fraction-field automorphisms.
Its group-theoretic norm agrees with the algebra norm, and invariant units
descend to units of the base ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

variable (R S K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S]

/-- Galois action on the units of the actual integral model. -/
def integralUnitRep : Rep ℤ Gal(L/K) :=
  Rep.of ((Rep.ofAlgebraAutOnUnits R S).ρ.comp (galRestrict R K L S).toMonoidHom)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
  [IsFractionRing S L] [FiniteDimensional K L] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] in
/-- The action is integral restriction on unit values. -/
@[simp] theorem integralUnitRep_action (g : Gal(L/K)) (u : Sˣ) :
    Additive.toMul ((integralUnitRep R S K L).ρ g (Additive.ofMul u)) =
      Units.map (galRestrict R K L S g).toMonoidHom u := rfl

omit [IsDiscreteValuationRing R] [IsDomain S] [IsDiscreteValuationRing S]
  [IsLocalHom (algebraMap R S)] in
/-- The representation norm is the integral algebra norm after inclusion. -/
theorem integralUnitRep_norm (u : Sˣ) :
    ((Additive.toMul ((integralUnitRep R S K L).norm.hom (Additive.ofMul u)) : Sˣ) : S) =
      algebraMap R S (Algebra.norm R (u : S)) := by
  classical
  apply IsFractionRing.injective S L
  rw [← IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply R K L,
    ← integral_norm_eq_field_norm R S K L, Algebra.norm_eq_prod_automorphisms]
  rw [Rep.norm_apply]
  simp only [Representation.norm, LinearMap.sum_apply]
  change algebraMap S L (↑(∏ g : Gal(L/K),
    Units.map (galRestrict R K L S g).toMonoidHom u) : S) = _
  rw [Units.coe_prod, map_prod]
  apply Finset.prod_congr rfl
  intro g _
  exact algebraMap_galRestrictHom_apply R K L S g (u : S)

omit [IsDomain S] [IsDiscreteValuationRing S] [Module.Free R S] [Module.Finite R S] in
/-- An invariant integral unit is the image of a base unit. -/
theorem integralUnitRep_invariant (u : Sˣ)
    (hu : ∀ g : Gal(L/K), Units.map (galRestrict R K L S g).toMonoidHom u = u) :
    ∃ v : Rˣ, Units.map (algebraMap R S) v = u := by
  let := IsIntegralClosure.MulSemiringAction R K L S
  let := Algebra.isInvariant_of_isGalois R K L S
  obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := R) (B := S) (G := Gal(L/K))
    (u : S) (fun g => congrArg Units.val (hu g))
  have hunit : IsUnit r := isUnit_of_map_unit (algebraMap R S) r (hr ▸ u.isUnit)
  refine ⟨hunit.unit, Units.ext ?_⟩
  change algebraMap R S (hunit.unit : R) = (u : S)
  rw [hunit.unit_spec, hr]

end LocalClassFieldTheory
