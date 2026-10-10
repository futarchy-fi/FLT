/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralShortHomologyNaturality
public import FLT.Mazur.ShortComplexSumHomologyInclusion

/-!
# Original component inclusions in additive direct-sum homology

Naturality of the integral comparison and the explicit finite-support quotient
calculation identify each inclusion under the existing additive equivalence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped DirectSum

namespace FLT.Mazur.AdditiveComplexDirectSum

open ProjectiveSpace.TwistCechCohomology

variable (K : ℕ → CochainComplex AddCommGrpCat.{0} ℕ)

/-- The original inclusion agrees with its integral short-complex inclusion. -/
lemma inclusion_integralShort (q n : ℕ) :
    integralShortMap
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℕ) q).map
          (inclusion K n)) ≫ (sumIntegralShortIso K q).hom =
      shortSumInclusion ℤ (fun k ↦ integralShort ((K k).sc q)) n := by
  ext <;> rfl

/-- The existing additive homology equivalence sends the actual inclusion to its summand. -/
lemma homologyEquiv_inclusion (q n : ℕ) (x : (K n).homology q) :
    homologyEquiv K q (HomologicalComplex.homologyMap (inclusion K n) q x) =
      DirectSum.of (fun k ↦ (K k).homology q) n x := by
  let φ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℕ) q).map
    (inclusion K n)
  change (DFinsupp.mapRange.addEquiv fun k ↦ (integralHomologyEquiv ((K k).sc q)).symm)
    ((shortSumHomologyIso ℤ (fun k ↦ integralShort ((K k).sc q))).hom
      (ShortComplex.homologyMap (sumIntegralShortIso K q).hom
        (integralHomologyEquiv ((complex K).sc q) (ShortComplex.homologyMap φ x)))) = _
  rw [integralHomologyEquiv_naturality]
  rw [← ModuleCat.comp_apply (ShortComplex.homologyMap (integralShortMap φ))
    (ShortComplex.homologyMap (sumIntegralShortIso K q).hom),
    ← ShortComplex.homologyMap_comp, inclusion_integralShort]
  rw [shortSumHomologyIso_inclusion]
  change DirectSum.map (fun k ↦ (integralHomologyEquiv ((K k).sc q)).symm.toAddMonoidHom)
    (DirectSum.of (fun k ↦ (integralShort ((K k).sc q)).homology) n
      (integralHomologyEquiv ((K n).sc q) x)) = _
  rw [DirectSum.map_of]
  change DirectSum.of (fun k ↦ (K k).homology q) n
    ((integralHomologyEquiv ((K n).sc q)).symm
      (integralHomologyEquiv ((K n).sc q) x)) = _
  rw [AddEquiv.symm_apply_apply]

end FLT.Mazur.AdditiveComplexDirectSum
