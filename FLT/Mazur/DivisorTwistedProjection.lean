/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCokernelProjection
public import FLT.Mazur.DivisorTwistedSequence

/-!
# The twisted quotient is actual restriction

The comparison from the tensorized divisor cokernel commutes with its
original quotient morphism and the pullback adjunction unit. This identifies
leading classes with restrictions of the original sections, including products.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The twisted quotient comparison intertwines the actual quotient and restriction maps. -/
theorem divisorTwistedQuotientIso_projection :
    (divisorTwistedComplex hI L).g ≫ (divisorTwistedQuotientIso hI L hL).hom =
      (pullbackPushforwardAdjunction I.subschemeι).unit.app
        (tensor (divisorLineBundle I hI) L) := by
  apply (cancel_mono ((pushforward I.subschemeι).map
    (tensorIso I.subschemeι (divisorLineBundle I hI) L).hom)).mp
  simp only [divisorTwistedQuotientIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  change map (Limits.cokernel.π (divisorSectionMap hI)) (𝟙 L) ≫
    map (divisorCokernelClosedIso hI).hom (𝟙 L) ≫
      ClosedLineProjectionFormula.comparison I.subschemeι _ L = _
  rw [← Category.assoc, ← ModuleSheafTensor.map_comp, Category.id_comp,
    divisorCokernelClosedIso_projection]
  apply ModuleSheafTensor.hom_ext
  intro U s t
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure,
    ClosedLineProjectionFormula.comparison_pure, Hom.id_app, ConcreteCategory.id_apply]
  exact (tensorIso_adj_pure I.subschemeι (divisorLineBundle I hI) L U s t).symm

end FLT.Mazur.FCurve
