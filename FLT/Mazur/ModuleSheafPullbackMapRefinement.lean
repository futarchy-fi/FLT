/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionLocalHom
public import FLT.Mazur.ModulePullbackUnitCoherence

/-!
# Refinement of pullback maps in restriction coordinates

Converting a pullback map to an ordinary open restriction commutes with
further open refinement. This connects geometric pullback coherence to
sectionwise compatibility on the image opens used for gluing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom

variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (t : Z ⟶ Y)
variable [IsOpenImmersion i] [IsOpenImmersion t]

/-- The two canonical ways to compare a composite restriction with iterated pullback agree. -/
lemma refinementIso (M : X.Modules) :
    (restrictFunctorIsoPullback (t ≫ i)).app M ≪≫ (pullbackComp t i).symm.app M =
      (restrictFunctorComp t i).app M ≪≫
        (restrictFunctor t).mapIso ((restrictFunctorIsoPullback i).app M) ≪≫
          (restrictFunctorIsoPullback t).app ((pullback i).obj M) := by
  apply Iso.ext
  exact (NatTrans.congr_app (FCurve.restrictFunctorIsoPullback_comp t i) M).symm

/-- Refining a geometric pullback map agrees with refining its ordinary restriction map. -/
lemma toRestriction_refine {M N : X.Modules}
    (a : (pullback i).obj M ⟶ (pullback i).obj N) :
    toRestriction (t ≫ i)
        ((pullbackComp t i).inv.app M ≫ (pullback t).map a ≫
          (pullbackComp t i).hom.app N) =
      (restrictFunctorComp t i).hom.app M ≫
        (restrictFunctor t).map (toRestriction i a) ≫
          (restrictFunctorComp t i).inv.app N := by
  have hM := congrArg Iso.hom (refinementIso i t M)
  have hN := congrArg Iso.inv (refinementIso i t N)
  dsimp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv] at hM hN
  dsimp only [toRestriction]
  simp only [Category.assoc, Functor.map_comp]
  rw [← Category.assoc ((restrictFunctorIsoPullback (t ≫ i)).hom.app M), hM]
  simp only [Category.assoc]
  rw [hN, ← (restrictFunctorIsoPullback t).hom.naturality_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
