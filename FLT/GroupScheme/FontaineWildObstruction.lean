/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineRelativeObstruction
public import FLT.GroupScheme.LocalPerturbedWitness
public import FLT.GroupScheme.LocalInertiaCriticalExponent

/-!
# The wild Fontaine obstruction

The critical inertia exponent lies above the relative Eisenstein degree.
Perturbing at that exponent constructs an exact-value witness of the same
absolute degree, and the relative polynomial obstruction excludes an embedding.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L] [IsGalois ℚ_[3] L]

/-- An inertia displacement exceeding one yields the corrected Fontaine
obstruction by a constructed Eisenstein perturbation. -/
theorem notFontainePropertyOfWildPresentation
    {C : Type} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra ℤ_[3] C] [Module.Finite ℤ_[3] C] [FaithfulSMul ℤ_[3] C]
    [Algebra C (ThreeAdicIntegers L)] [IsScalarTower ℤ_[3] C (ThreeAdicIntegers L)]
    [FaithfulSMul C (ThreeAdicIntegers L)] [Algebra.FormallyUnramified ℤ_[3] C]
    (pc : PowerBasis ℤ_[3] C) (pb : PowerBasis C (ThreeAdicIntegers L))
    (h3 : Irreducible (3 : C))
    (hP : (minpoly C pb.gen).IsEisensteinAt (maximalIdeal C))
    (hdim : pb.dim = threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}))
    (c : ℕ) (hc : 1 < c)
    (hbound : ∀ σ : ThreeAdicIntegralInertia L, σ ≠ 1 →
      threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom) ≤ c)
    (hmax : ∃ σ : ThreeAdicIntegralInertia L, σ ≠ 1 ∧
      threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom) = c)
    (m : ℚ) (hm : m ≤
      ((threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) + c - 1 : ℕ) : ℚ) /
        threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)})) :
    ¬ FontaineProperty (ThreeAdicIntegers L) m := by
  let N := threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) + c - 1
  have hN : (minpoly C pb.gen).natDegree < N := by
    have hD := threeAdicDifferentOrderGeRamificationOfWild L pc pb c hc hmax
    rw [pb.natDegree_minpoly, hdim]
    dsimp [N]
    omega
  have hn : 0 < (minpoly C pb.gen).natDegree := by
    rw [pb.natDegree_minpoly, hdim]
    exact threeAdicIdealOrder_three_pos L
  obtain ⟨E, instField, instAlgQ, instAlgZ, instTower, instFinite, instAlgC,
    instTowerC, instFaithfulC, y, hdegree, hram, hy⟩ :=
      existsThreeAdicPerturbedWitness h3 hP (minpoly.monic pb.isIntegral_gen) hn N hN
  let instFiniteC : Module.Finite C (ThreeAdicIntegers L) := pb.finite
  have hdeg : Module.finrank ℚ_[3] E ≤ Module.finrank ℚ_[3] L := by
    rw [hdegree, pb.natDegree_minpoly,
      IsFractionRing.finrank_eq ℤ_[3] ℚ_[3] (ThreeAdicIntegers L) L,
      ← Module.finrank_mul_finrank ℤ_[3] C (ThreeAdicIntegers L), pb.finrank]
  apply notFontainePropertyOfRelativeApproximateRoot L E pb m y
  · apply threeAdicMemValuationIdealOfAddVal E _ N hy m
    simpa only [hram, pb.natDegree_minpoly, hdim] using hm
  · exact threeAdicRelativeNoEmbeddingOfExcludedValue L E pc _ N
      (threeAdicRelativeMinpolyAddValNeCritical L pc pb hdim c hbound hmax (by omega))
      hdeg y hy

end ThreeAdicPlan
