/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedOrderSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Normalized order for ramified extensions

Integral restriction carries a uniformizer to a uniformizer. Thus normalized
order is Galois invariant without an unramifiedness assumption, and gives
the short exact valuation sequence for every finite local Galois extension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable (R S K L : Type) [CommRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [IsGalois K L]


include R in
/-- Integral restriction preserves normalized order even in ramified extensions. -/
theorem discreteOrder_galois_ramified (g : Gal(L/K)) (x : Lˣ) :
    discreteOrder S L (Units.map g.toMonoidHom x) = discreteOrder S L x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  let σ := galRestrict R K L S g
  have hσ : Irreducible (σ π) := hπ.map σ.toMulEquiv
  have hπmap : Units.map g.toMonoidHom (fractionUniformizer S L hπ) =
      fractionUniformizer S L hσ := by
    apply Units.ext
    exact (algebraMap_galRestrictHom_apply R K L S g π).symm
  obtain ⟨u, n, rfl⟩ := exists_unit_mul_fractionUniformizer_zpow S L hπ x
  have hmap : Units.map g.toMonoidHom (Units.map (algebraMap S L) u) =
      Units.map (algebraMap S L) (Units.map σ.toMonoidHom u) := by
    apply Units.ext
    exact (algebraMap_galRestrictHom_apply R K L S g (u : S)).symm
  rw [map_mul, map_zpow, hmap, hπmap]
  simp

/-- Normalized order as a morphism to the trivial integer representation. -/
def ramifiedOrderMap : Rep.ofAlgebraAutOnUnits K L ⟶ Rep.trivial ℤ Gal(L/K) ℤ :=
  Rep.ofHom ⟨(discreteOrderAdd S L).toIntLinearMap, fun g => by
    ext x
    exact congrArg Multiplicative.toAdd (discreteOrder_galois_ramified R S K L g x.toMul)⟩

/-- The composite is zero because integral units have order zero. -/
theorem integralUnitInclusion_ramifiedOrder :
    integralUnitInclusion R S K L ≫ ramifiedOrderMap R S K L = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  change (discreteOrder S L (Units.map (algebraMap S L) u.toMul)).toAdd = 0
  rw [discreteOrder_unit]
  rfl

/-- The order sequence as a short complex of Galois representations. -/
def ramifiedOrderSequence : ShortComplex (Rep ℤ Gal(L/K)) :=
  ShortComplex.mk (integralUnitInclusion R S K L) (ramifiedOrderMap R S K L)
    (integralUnitInclusion_ramifiedOrder R S K L)

/-- Exactness uses the proved description of the order kernel and surjectivity. -/
theorem ramifiedOrderSequence_shortExact :
    (ramifiedOrderSequence R S K L).ShortExact where
  mono_f := (Rep.mono_iff_injective _).2 (by
    intro x y h
    apply Additive.toMul.injective
    exact Units.map_injective (IsFractionRing.injective S L) h)
  epi_g := (Rep.epi_iff_surjective _).2 (by
    intro n
    obtain ⟨x, hx⟩ := discreteOrder_surjective S L (Multiplicative.ofAdd n)
    exact ⟨Additive.ofMul x, congrArg Multiplicative.toAdd hx⟩)
  exact := by
    apply representation_exact_of_functions
    intro x hx
    have hx' : discreteOrder S L x.toMul = 1 := congrArg Multiplicative.ofAdd hx
    obtain ⟨u, hu⟩ := (discreteOrder_eq_one_iff S L x.toMul).1 hx'
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩

end LocalClassFieldTheory
