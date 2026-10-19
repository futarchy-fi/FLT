/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupPointClassification
public import FLT.Mazur.WeierstrassSubgroupFactorization
public import FLT.Mazur.WeierstrassUniversalComparisonClassification

/-!
# The closed comparison scheme classifies full compatible subgroup isomorphisms

Every affine test of the actual closed locus corresponds uniquely to a
compatible comparison of the original full subgroups. No choice of Cartier
generator or etaleness hypothesis is involved.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) {n : ℕ}
  (H : (integralGeneralizedEllipticCurve W hW).FiniteSubgroup n)
  (J : (integralGeneralizedEllipticCurve V hV).FiniteSubgroup n)
  (A : Type) [CommRing A] [Algebra R A]
local notation "q" => comparisonStructure W V
local notation "i" => subgroupInclusion W V hW hV H J
local notation "s" => subgroupStructure W V hW hV H J
local notation "t" => Spec.algebraMap R A

/-- An affine full comparison preserves the subgroups exactly on the closed parameter locus. -/
theorem subgroupPoint_factorization_iff
    (f : {f : Spec (.of A) ⟶ comparisonScheme W V // f ≫ q = t}) :
    (∃ k : Spec (.of A) ⟶ subgroupScheme W V hW hV H J, k ≫ i = f.val) ↔
      ∃ a : CompatibleIso (H.baseChange t) (J.baseChange t),
        a.curve = generalizedComparisonPointEquiv W V hW hV f := by
  simpa only [generalizedComparisonPointEquiv_apply, universalComparisonOnTest] using
    subgroupInclusion_factorization_comp_iff W V hW hV H J f.val t f.property.symm

/-- Points of the actual closed comparison scheme classify every compatible subgroup comparison. -/
def subgroupPointEquiv :
    {k : Spec (.of A) ⟶ subgroupScheme W V hW hV H J // k ≫ s = t} ≃
      CompatibleIso (H.baseChange t) (J.baseChange t) :=
  subgroupTestPointEquiv H J i q t (generalizedComparisonPointEquiv W V hW hV)
    (subgroupPoint_factorization_iff W V hW hV H J A)

/-- The closed classifier keeps the exact pullback of the universal full comparison. -/
theorem subgroupPointEquiv_curve
    (k : {k : Spec (.of A) ⟶ subgroupScheme W V hW hV H J // k ≫ s = t}) :
    (subgroupPointEquiv W V hW hV H J A k).curve =
      universalComparisonOnTest W V hW hV (subgroupTestForget i q t k) := by
  rw [← generalizedComparisonPointEquiv_apply]
  exact subgroupTestPointEquiv_curve H J i q t _ _ k

/-- Each prescribed compatible comparison has precisely one actual closed-locus parameter. -/
theorem subgroupPointEquiv_unique (a : CompatibleIso (H.baseChange t) (J.baseChange t)) :
    ∃! k : {k : Spec (.of A) ⟶ subgroupScheme W V hW hV H J // k ≫ s = t},
      subgroupPointEquiv W V hW hV H J A k = a :=
  (subgroupPointEquiv W V hW hV H J A).bijective.existsUnique a

end FLT.Mazur.WeierstrassChangeParameter
