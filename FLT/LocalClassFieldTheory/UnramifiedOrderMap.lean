/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DiscreteOrderExact
public import FLT.LocalClassFieldTheory.IntegralUnitRepresentation

/-!
# The equivariant order sequence

An unramified base uniformizer is fixed by Galois. Uniformizer factorization
therefore makes order a morphism to the trivial integer representation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable (R S K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [IsLocalHom (algebraMap R S)]
  [Module.Finite R S] [Algebra.FormallyUnramified R S]

omit [FiniteDimensional K L] in
include R in
/-- Galois preserves classical order in an unramified integral extension. -/
theorem discreteOrder_galois (g : Gal(L/K)) (x : Lˣ) :
    discreteOrder S L (Units.map g.toMonoidHom x) = discreteOrder S L x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hs := unramified_uniformizer_irreducible R S hπ
  have hfix : Units.map g.toMonoidHom (fractionUniformizer S L hs) =
      fractionUniformizer S L hs := by
    apply Units.ext
    change g (algebraMap S L (algebraMap R S π)) = algebraMap S L (algebraMap R S π)
    rw [← IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply R K L,
      g.commutes]
  obtain ⟨u, n, rfl⟩ := exists_unit_mul_fractionUniformizer_zpow S L hs x
  have hmap : Units.map g.toMonoidHom (Units.map (algebraMap S L) u) =
      Units.map (algebraMap S L) (Units.map (galRestrict R K L S g).toMonoidHom u) := by
    apply Units.ext
    exact (algebraMap_galRestrictHom_apply R K L S g (u : S)).symm
  rw [map_mul, map_zpow, hfix, hmap, map_mul, map_mul,
    discreteOrder_unit, discreteOrder_unit]

/-- Inclusion of integral units in fraction-field units, with the actual Galois actions. -/
def integralUnitInclusion : integralUnitRep R S K L ⟶ Rep.ofAlgebraAutOnUnits K L :=
  Rep.ofHom ⟨(Units.map (algebraMap S L)).toAdditive.toIntLinearMap, fun g => by
    ext u
    exact algebraMap_galRestrictHom_apply R K L S g (Additive.toMul u : Sˣ)⟩

/-- The integer order map as an additive homomorphism. -/
def discreteOrderAdd : Additive Lˣ →+ ℤ where
  toFun x := (discreteOrder S L x.toMul).toAdd
  map_zero' := by simp
  map_add' x y := by
    change (discreteOrder S L (x.toMul * y.toMul)).toAdd = _
    rw [map_mul]
    rfl

/-- Order as a morphism of Galois representations. -/
def unramifiedOrderMap : Rep.ofAlgebraAutOnUnits K L ⟶ Rep.trivial ℤ Gal(L/K) ℤ :=
  Rep.ofHom ⟨(discreteOrderAdd S L).toIntLinearMap, fun g => by
    ext x
    exact congrArg Multiplicative.toAdd (discreteOrder_galois R S K L g x.toMul)⟩

end LocalClassFieldTheory
