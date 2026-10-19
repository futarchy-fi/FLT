/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSubgroupComparisonLocus
public import FLT.Mazur.CompatibleSubgroupIsoConjugation

/-!
# The full subgroup comparison locus commutes with composite tests

For every scheme test, restricting the prescribed comparison before testing
its subgroup condition agrees with testing along the composite base map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n) (e : E ≅ F)
  (g : T ⟶ S) (h : U ⟶ T)

/-- The direct and iterated pullbacks give the identical prescribed full comparison. -/
theorem subgroupComparison_curve_comp :
    E.baseChangeCompIso g h ≪≫ (baseChangeFunctor h).mapIso
      ((baseChangeFunctor g).mapIso e) ≪≫ (F.baseChangeCompIso g h).symm =
        (baseChangeFunctor (h ≫ g)).mapIso e := by
  apply Iso.ext
  apply (cancel_mono (F.baseChangeCompIso g h).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  exact ((baseChangeComp g h).hom.naturality e.hom).symm

/-- Tests of the restricted comparison locus are exactly composite tests of the original. -/
theorem subgroupComparisonLocus_factorization_baseChange_iff :
    (∃ k : U ⟶ subgroupComparisonLocus (H.baseChange g) (J.baseChange g)
      ((baseChangeFunctor g).mapIso e),
      k ≫ subgroupComparisonLocusInclusion (H.baseChange g) (J.baseChange g)
        ((baseChangeFunctor g).mapIso e) = h) ↔
    ∃ k : U ⟶ subgroupComparisonLocus H J e,
      k ≫ subgroupComparisonLocusInclusion H J e = h ≫ g := by
  rw [subgroupComparisonLocus_factorization_iff, subgroupComparisonLocus_factorization_iff]
  have hc := compatibleIso_exists_conjugate_iff
    (compatibleBaseChangeComp H g h).symm (compatibleBaseChangeComp J g h).symm
    ((baseChangeFunctor h).mapIso ((baseChangeFunctor g).mapIso e))
  simpa only [CompatibleIso.symm, CompatibleIso.baseChange, transportCompatibleIso,
    compatibleBaseChangeComp, Iso.symm_symm_eq, subgroupComparison_curve_comp] using hc

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
