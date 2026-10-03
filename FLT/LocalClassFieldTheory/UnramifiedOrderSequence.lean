/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedOrderMap
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# The short exact unramified order sequence

The sequence of integral units, fraction-field units, and integer order is
short exact as a sequence of actual Galois representations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

/-- Exactness of representation morphisms can be checked on their underlying modules. -/
theorem representation_exact_of_functions {k G : Type} [CommRing k] [Group G]
    (X : ShortComplex (Rep k G))
    (h : ∀ x, X.g.hom x = 0 → ∃ y, X.f.hom y = x) : X.Exact := by
  rw [← X.exact_map_iff_of_faithful (forget₂ (Rep k G) (ModuleCat k))]
  exact (ShortComplex.moduleCat_exact_iff _).2 h

variable (R S K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [IsGalois K L] [IsLocalHom (algebraMap R S)]
  [Module.Finite R S] [Algebra.FormallyUnramified R S]

/-- The composite is zero because integral units have order zero. -/
theorem integralUnitInclusion_order :
    integralUnitInclusion R S K L ≫ unramifiedOrderMap R S K L = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  change (discreteOrder S L (Units.map (algebraMap S L) u.toMul)).toAdd = 0
  rw [discreteOrder_unit]
  rfl

/-- The order sequence as a short complex of Galois representations. -/
def unramifiedOrderSequence : ShortComplex (Rep ℤ Gal(L/K)) :=
  ShortComplex.mk (integralUnitInclusion R S K L) (unramifiedOrderMap R S K L)
    (integralUnitInclusion_order R S K L)

/-- Exactness uses the proved description of the order kernel and surjectivity. -/
theorem unramifiedOrderSequence_shortExact :
    (unramifiedOrderSequence R S K L).ShortExact where
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
