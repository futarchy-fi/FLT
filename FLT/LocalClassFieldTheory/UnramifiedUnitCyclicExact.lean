/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralUnitRepresentation
public import FLT.LocalClassFieldTheory.UnitNormSurjectivity

/-!
# Exactness of the cyclic unit complexes

Unit norm surjectivity proves the even complex exact; integral unit Hilbert 90
proves the odd complex exact. These are the actual periodic cohomology complexes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory IsLocalRing Rep.FiniteCyclicGroup

variable (R S K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [IsCyclic Gal(L/K)]

attribute [local instance] IsCyclic.commGroup

/-- The cyclic odd complex of units is exact by integral unit Hilbert 90. -/
theorem integralUnit_odd_exact (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    (subCompNormHom (integralUnitRep R S K L) g).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : algebraMap R S (Algebra.norm R ((Additive.toMul x : Sˣ) : S)) = 1 := by
    rw [← integralUnitRep_norm R S K L]
    change ((Additive.toMul ((integralUnitRep R S K L).norm.hom x) : Sˣ) : S) = 1
    rw [show (integralUnitRep R S K L).norm.hom x = 0 from hx]
    rfl
  have hi : Function.Injective (algebraMap R S) := by
    intro a b hab
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    simpa only [← IsScalarTower.algebraMap_apply] using congrArg (algebraMap S L) hab
  have hn : Algebra.norm R ((Additive.toMul x : Sˣ) : S) = 1 := hi (hx'.trans (map_one _).symm)
  obtain ⟨v, hv⟩ := unramified_unit_hilbert90 R S K L g hg (Additive.toMul x) hn
  refine ⟨Additive.ofMul v, ?_⟩
  apply Additive.toMul.injective
  exact hv

/-- The cyclic even complex of units is exact by the proved unit norm surjectivity. -/
theorem integralUnit_even_exact [Finite (ResidueField R)]
    [IsAdicComplete (maximalIdeal R) R]
    (g : Gal(L/K)) (hg : ∀ σ, σ ∈ Subgroup.zpowers g) :
    (normHomCompSub (integralUnitRep R S K L) g).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hgx : (integralUnitRep R S K L).ρ g x = x := sub_eq_zero.mp hx
  have hinv := (Representation.mem_invariants_iff_of_forall_mem_zpowers
    (integralUnitRep R S K L).ρ g hg x).2 hgx
  obtain ⟨u, hu⟩ := integralUnitRep_invariant R S K L (Additive.toMul x)
    (fun σ => congrArg Additive.toMul (hinv σ))
  obtain ⟨v, hv⟩ := unramified_unit_norm_surjective R S u
  refine ⟨Additive.ofMul v, ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  change ((Additive.toMul ((integralUnitRep R S K L).norm.hom (Additive.ofMul v)) : Sˣ) : S) = _
  rw [integralUnitRep_norm R S K L]
  have hv' : Algebra.norm R (v : S) = (u : R) := congrArg Units.val hv
  rw [hv']
  exact congrArg Units.val hu

end LocalClassFieldTheory
