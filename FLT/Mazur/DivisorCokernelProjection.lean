/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorClosedCokernel
public import FLT.Mazur.LineStructureProjection

/-!
# The divisor cokernel comparison retains the quotient morphism

The canonical cokernel isomorphism carries the actual cokernel projection
to restriction of the divisor line to the closed divisor.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- The tensor cokernel comparison retains the original closed quotient map. -/
@[reassoc]
theorem divisorCokernelTensorIso_projection :
    (leftUnitor (divisorLineBundle I hI)).hom ≫ cokernel.π (divisorSectionMap hI) ≫
      (divisorCokernelTensorIso hI).hom =
        map (idealQuotientMap I) (𝟙 (divisorLineBundle I hI)) := by
  let S := (idealQuotientComplex I).map
    (ModuleSheafTensorCurrying.tensoring (divisorLineBundle I hI))
  have hc := IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel S.f)
    (divisorTensorSequence_shortExact hI).gIsCokernel WalkingParallelPair.one
  change cokernel.π S.f ≫ _ = S.g at hc
  simp only [divisorCokernelTensorIso, Iso.trans_hom, Iso.symm_hom,
    cokernel.mapIso, cokernel.map, cokernel.π_desc_assoc]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact hc

/-- The closed cokernel projection is precisely the pullback adjunction unit. -/
theorem divisorCokernelClosedIso_projection :
    cokernel.π (divisorSectionMap hI) ≫ (divisorCokernelClosedIso hI).hom =
      (pullbackPushforwardAdjunction I.subschemeι).unit.app (divisorLineBundle I hI) := by
  apply (cancel_epi (leftUnitor (divisorLineBundle I hI)).hom).mp
  change (leftUnitor (divisorLineBundle I hI)).hom ≫ cokernel.π (divisorSectionMap hI) ≫
    (divisorCokernelTensorIso hI).hom ≫
      (LineStructureProjection.iso I.subschemeι (divisorLineBundle I hI)
        hI.divisorLineBundle_locallyFreeRankOne).hom = _
  rw [divisorCokernelTensorIso_projection_assoc]
  exact LineStructureProjection.unit_compatibility I.subschemeι _
    hI.divisorLineBundle_locallyFreeRankOne

end FLT.Mazur.FCurve
