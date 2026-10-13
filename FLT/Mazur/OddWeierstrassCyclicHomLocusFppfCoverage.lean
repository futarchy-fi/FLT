/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomUniversalSubgroupComparison
public import FLT.Mazur.OddWeierstrassCyclicHomDivisorFppfCoverage

/-!
# Odd-chart original cyclic subgroup covers factor through the global closed locus

The existing fppf cover retains the full original subgroup and its Cartier
generator. Each unchanged auxiliary parameter factors through the actual
global multiplication locus. The original coverage hypotheses are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) (hc : H.IsCyclic)
  (h₃ : IsUnit (3 : Γ(S, ⊤)))

include hc h₃ in
/-- The original finite subgroup cover has actual points of the global closed cyclic locus. -/
theorem exists_hom_locus_fppf_cover [Smooth E.curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (p : ∀ i : C.I₀, C.X i ⟶ (cyclicHomAuxiliaryScheme n).left)
      (q : ∀ i : C.I₀, C.X i ⟶ cyclicHomUniversalMultiplicationLocus n)
      (J : ∀ i, (cyclicHomSourceCurve n (p i)).FiniteSubgroup n),
      ∀ i, q i ≫ cyclicHomUniversalMultiplicationLocusInclusion n = p i ∧
        (J i).ideal = cyclicHomSourceIdeal n (p i) ∧
          (∃ P, (J i).IsCartierGenerator P) ∧
            Nonempty (CompatibleIso (J i) (H.baseChange (C.f i))) := by
  obtain ⟨C, p, J, hJ⟩ := exists_hom_divisor_fppf_cover H hc h₃
  have hz i := cyclicHomMultiplicationEquation_of_subgroup n (p i) (J i) (hJ i).1
  exact ⟨C, p, (fun i ↦ cyclicHomUniversalLocusLift n (p i) (hz i)), J,
    fun i ↦ ⟨cyclicHomUniversalLocusLift_inclusion n (p i) (hz i), hJ i⟩⟩

include hc h₃ in
/-- The actual universal subgroup covers every original smooth cyclic subgroup fppf locally. -/
theorem exists_universal_hom_subgroup_fppf_cover [Smooth E.curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (q : ∀ i : C.I₀, C.X i ⟶ cyclicHomUniversalMultiplicationLocus n),
      ∀ i, Nonempty (CompatibleIso ((cyclicHomUniversalSubgroup n).baseChange (q i))
        (H.baseChange (C.f i))) := by
  obtain ⟨C, p, q, J, hJ⟩ := exists_hom_locus_fppf_cover H hc h₃
  refine ⟨C, q, fun i ↦ ?_⟩
  obtain ⟨a⟩ := (hJ i).2.2.2
  exact ⟨(cyclicHomUniversalSubgroupIsoOfFactorization n (q i) (p i)
    (hJ i).1 (J i) (hJ i).2.1).trans a⟩

end FLT.Mazur.OddWeierstrassParameter
