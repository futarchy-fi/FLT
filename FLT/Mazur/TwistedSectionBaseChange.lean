/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectImageBaseChangeAdjoints
public import FLT.Mazur.LineDualPullbackSquare
public import FLT.Mazur.LineTensorSectionPullback
public import FLT.Mazur.LineTensorSectionTransport

/-!
# Twisted sections commute with actual direct-image base change

The section on the new total space is obtained by geometric pullback and the
original square comparison. Its direct-image map is the Beck-Chevalley mate
of the original map, transported through the canonical dual-line isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor SchemePullbackSquare DirectImageBaseChange
attribute [local irreducible] ModuleSheafTensor.tensor ModuleLineBundleTensorPullback.tensorIso
variable {P X T S : Scheme.{u}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (L : X.Modules) {B : S.Modules} (hB : LocallyFreeRankOne B)

/-- Geometric pullback of a twisted section gives the actual base-changed direct-image map. -/
lemma twistedSectionPushforwardEquiv_baseChange
    (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    twistedSectionPushforwardEquiv q ((pullback p).obj L) (hB.pullback g)
        ((map (𝟙 _) ((squareIso f q g p w).inv.app B)).app ⊤
          ((ModuleLineBundleTensorPullback.tensorIso p L ((pullback f).obj B)).hom.app ⊤
            (pullGlobal p _ s))) =
      (moduleSheafDualPullbackIso g hB).inv ≫
        (pullback g).map (twistedSectionPushforwardEquiv f L hB s) ≫
          comparison p q f g w L := by
  rw [← cancel_epi (moduleSheafDualPullbackIso g hB).hom, Iso.hom_inv_id_assoc]
  apply ((pullbackPushforwardAdjunction q).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, twistedSectionPushforwardEquiv_adjoint]
  have ht := lineHomSectionEquiv_symm_transport ((hB.pullback f).pullback p)
    ((hB.pullback g).pullback q) ((squareIso f q g p w).app B).symm
    ((pullback p).obj L)
    ((ModuleLineBundleTensorPullback.tensorIso p L ((pullback f).obj B)).hom.app ⊤
      (pullGlobal p _ s))
  dsimp only [Iso.symm_hom, Iso.app_inv, Functor.comp_obj] at ht
  erw [ht]
  rw [lineHomSectionEquiv_symm_pullback, twistedSection_comparison_adjoint]
  exact moduleSheafDualPullbackIso_square_map p q f g w hB _

end FLT.Mazur.FCurve
