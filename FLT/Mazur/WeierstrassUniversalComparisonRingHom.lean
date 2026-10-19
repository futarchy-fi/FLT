/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassUniversalComparisonSpecialization

/-!
# Universal comparison specialization with named coefficient equations

An arbitrary ring homomorphism from the comparison algebra gives the actual
full comparison on separately named coefficient models.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type} [CommRing R] [CommRing A]
  (W V : WeierstrassCurve R) (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
  (p : EquationRing W V →+* A) (t : R →+* A)
  (ht : t = p.comp (algebraMap R (EquationRing W V)))
  (W' V' : WeierstrassCurve A) (hW' : IsUnit W'.Δ) (hV' : IsUnit V'.Δ)
  (hw : W' = W.map t) (hv : V' = V.map t)
  (C : VariableChange A) (hc : C = (equationChange W V).map p) (he : C • V' = W')

include hc in
/-- Named coefficient models retain the full universal comparison under every ring test. -/
theorem universalComparisonOnRingHom_eq :
    comparisonPullback _ _ (comparisonStructure W V) (Spec.map (CommRingCat.ofHom p))
      (Spec.map (CommRingCat.ofHom t))
      (by
        rw [ht]
        exact Spec.map_comp (CommRingCat.ofHom (algebraMap R _)) (CommRingCat.ofHom p))
      (universalGeneralizedComparison W V hW hV) =
    (coefficientPresentationIso W hW t W' hW' hw).symm ≪≫
      changeGeneralizedIso W' V' hW' hV' C he ≪≫
        coefficientPresentationIso V hV t V' hV' hv := by
  subst W' V' C
  let _ : Algebra R A := t.toAlgebra
  let a : EquationRing W V →ₐ[R] A := ⟨p, DFunLike.congr_fun ht.symm⟩
  have h := universalComparisonOnAlgebra_eq W V hW hV a
  rw [changeBaseGeneralizedIso_eq] at h
  simpa only [universalComparisonOnAlgebra, coefficientPresentationIso,
    eqToIso_refl, Iso.refl_trans, comparisonStructure, Spec.algebraMap, a,
    RingHom.algebraMap_toAlgebra] using h

end FLT.Mazur.WeierstrassChangeParameter
