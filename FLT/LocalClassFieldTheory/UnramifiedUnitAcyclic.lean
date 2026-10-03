/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedUnitCyclicExact
public import FLT.LocalClassFieldTheory.Frobenius

/-!
# Acyclicity of units in finite unramified extensions

Arithmetic Frobenius supplies the cyclic generator. The proved exactness of
both periodic complexes kills every positive group-cohomology degree.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory Limits IsLocalRing Rep.FiniteCyclicGroup

variable (R S K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [Finite (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]

/-- Every positive cohomology group of the integral units vanishes. -/
theorem unramified_unit_cohomology_isZero (n : ℕ) :
    IsZero (groupCohomology (integralUnitRep R S K L) (n + 1)) := by
  let g := arithmeticFrobenius R S K L
  have hg : ∀ σ, σ ∈ Subgroup.zpowers g := by
    intro σ
    obtain ⟨i, rfl⟩ := arithmeticFrobenius_pow_surjective R S K L σ
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  let : IsCyclic Gal(L/K) := ⟨⟨g, hg⟩⟩
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  let A := integralUnitRep R S K L
  by_cases he : Even (n + 1)
  · exact ((ShortComplex.exact_iff_isZero_homology _).1
      (integralUnit_even_exact R S K L g hg)).of_iso
      (groupCohomologyIsoEven A g hg (n + 1) he)
  · exact ((ShortComplex.exact_iff_isZero_homology _).1
      (integralUnit_odd_exact R S K L g hg)).of_iso
      (groupCohomologyIsoOdd A g hg (n + 1) (Nat.not_even_iff_odd.mp he))

end LocalClassFieldTheory
