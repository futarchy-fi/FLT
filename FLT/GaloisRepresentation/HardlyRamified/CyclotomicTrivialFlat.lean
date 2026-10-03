/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.CyclotomicCharacterNaturality
public import FLT.Deformations.RepresentationTheory.FlatPadic
public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivialReduction
public import FLT.GroupScheme.SplitKummerResidue

/-! # Flatness of the actual cyclotomic-plus-trivial representation

The split Kummer model is constructed over the integers of the rational-place
completion itself. Cofinality then handles every open coefficient ideal.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
open NumberField IsDedekindDomain
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace GaloisRepresentation
variable (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ℚ))

set_option maxHeartbeats 800000 in
-- Tensor and geometric-point actions use several definitionally equal local structures.
/-- Every p-power quotient has a finite-flat prolongation over the actual local integers. -/
theorem cyclotomicTrivial_power_flat (n : ℕ) :
    ((cyclotomicTrivial p).baseChange
      (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ n})).HasFlatProlongationAt v := by
  let O := v.adicCompletionIntegers ℚ
  let K := v.adicCompletion ℚ
  let X := ThreeAdicPlan.generalSplitKummerModel O K p n
  let ρ := ((cyclotomicTrivial p).baseChange
    (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ n})).toLocal v
  let e : X.Points ≃+ ρ.Space :=
    (ThreeAdicPlan.splitKummerResidue O K p n).trans (cyclotomicTrivialReduction p n).symm
  have he (x : X.Points) : cyclotomicTrivialReduction p n (e x) =
      ThreeAdicPlan.splitKummerResidue O K p n x :=
    (cyclotomicTrivialReduction p n).apply_symm_apply _
  let f : X.Points →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] ρ.Space :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro g x
        apply (cyclotomicTrivialReduction p n).injective
        change cyclotomicTrivialReduction p n (e (g • x)) =
          cyclotomicTrivialReduction p n (ρ g (e x))
        rw [he]
        change ThreeAdicPlan.splitKummerResidue O K p n (g • x) =
          cyclotomicTrivialReduction p n
            ((cyclotomicTrivial p (Field.absoluteGaloisGroup.map (algebraMap ℚ K) g)).baseChange
              (PrimePower.Quot (p : ℤ_[p]) n) (e x))
        rw [cyclotomicTrivialReduction_action, ThreeAdicPlan.splitKummerResidue_smul]
        rw [he, integralCyclotomicScalar_apply, cyclotomicCharacter.absoluteGalois_map] }
  exact (ThreeAdicPlan.generalSplitKummer_isFiniteFlat O K p n).map O K
    (AlgebraicClosure K) X.Points f e.bijective

/-- Flatness holds for every open ideal, at every rational finite place. -/
theorem cyclotomicTrivial_isFlatAt : (cyclotomicTrivial p).IsFlatAt v :=
  (GaloisRep.isFlatAt_iff_powers p v (cyclotomicTrivial p)).mpr
    (cyclotomicTrivial_power_flat p v)

end GaloisRepresentation
