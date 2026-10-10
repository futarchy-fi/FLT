/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectImageBaseChangeUnit
public import FLT.Mazur.ClosedPushforwardRestriction

/-!
# Open base change for the actual direct-image mate

The explicit open restriction isomorphism equals the comparison constructed
from pullback adjunctions. Its invertibility needs no finiteness, flatness,
or Noetherian hypothesis on the morphism, base, or coefficient sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.DirectImageBaseChange
open FCurve.CoherentDevissage
universe u
/-- The restriction and pullback units agree under their canonical comparison. -/
lemma open_pullback_unit {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (M : Z.Modules) :
    (restrictAdjunction j).unit.app M ≫
      (pushforward j).map ((restrictFunctorIsoPullback j).hom.app M) =
        (pullbackPushforwardAdjunction j).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ _

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)

/-- The explicit open restriction isomorphism has the original restriction unit. -/
lemma open_restrict_unit (M : X.Modules) :
    (restrictAdjunction U.ι).unit.app ((pushforward f).obj M) ≫
      (pushforward U.ι).map ((closedPushforwardRestriction f U).hom.app M) =
    (pushforward f).map ((restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M) ≫
      ((pushforwardComp (f ⁻¹ᵁ U).ι f).hom ≫
        (pushforwardCongr (morphismRestrict_ι f U)).inv ≫
          (pushforwardComp (f ∣_ U) U.ι).inv).app (M.restrict (f ⁻¹ᵁ U).ι) := by
  ext V x
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    restrictAdjunction_unit_app_app, closedPushforwardRestriction_hom_app,
    NatTrans.comp_app, pushforwardComp_hom_app_app, pushforwardCongr_inv_app_app,
    pushforwardComp_inv_app_app]
  simp only [restrict_map]
  change M.presheaf.map _ (M.presheaf.map _ x) =
    M.presheaf.map _ (M.presheaf.map _ x)
  simp only [← Functor.map_comp_apply]
  rfl

/-- Restricting the actual direct image commutes with pullback to a base open. -/
@[irreducible] def openIso (M : X.Modules) :
    (pullback U.ι).obj ((pushforward f).obj M) ≅
      (pushforward (f ∣_ U)).obj ((pullback (f ⁻¹ᵁ U).ι).obj M) :=
  ((restrictFunctorIsoPullback U.ι).app _).symm ≪≫
    (closedPushforwardRestriction f U).app M ≪≫
      (pushforward (f ∣_ U)).mapIso ((restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app M)

/-- The explicit restriction isomorphism is the independently defined base-change mate. -/
lemma openIso_eq_comparison (M : X.Modules) :
    (openIso f U M).hom =
      comparison (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι (morphismRestrict_ι f U) M := by
  apply ((pullbackPushforwardAdjunction U.ι).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, comparison_unit_map]
  rw [← open_pullback_unit U.ι]
  rw [openIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← (pushforward U.ι).map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc,
    open_restrict_unit]
  rw [← open_pullback_unit (f ⁻¹ᵁ U).ι]
  simp only [Functor.map_comp, Category.assoc]
  have hn := ((pushforwardComp (f ⁻¹ᵁ U).ι f).hom ≫
    (pushforwardCongr (morphismRestrict_ι f U)).inv ≫
      (pushforwardComp (f ∣_ U) U.ι).inv).naturality
        ((restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).hom.app M)
  simpa only [Functor.comp_map, Category.assoc] using congrArg
    (fun k ↦ (pushforward f).map ((restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M) ≫ k)
      hn.symm

/-- The original base-change mate is invertible on every base open. -/
theorem openComparison_isIso (M : X.Modules) :
    IsIso (comparison (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι (morphismRestrict_ι f U) M) := by
  rw [← openIso_eq_comparison]
  infer_instance

end FLT.Mazur.DirectImageBaseChange
