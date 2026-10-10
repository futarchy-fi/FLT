/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTensorEquivalence

/-!
# Cancelling a fixed left line factor from an actual isomorphism

The concrete right-tensor equivalence and symmetry recover an isomorphism
of the remaining factors. Tensoring it again returns the specified map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleSheafTensorAssociator
variable {X : Scheme.{u}} {L M N : X.Modules}

/-- Symmetry intertwines the concrete maps in the two tensor orders. -/
lemma tensor_comm_map (a : M ⟶ N) :
    (comm M L).hom ≫ map (𝟙 L) a = map a (𝟙 L) ≫ (comm N L).hom := by
  apply ModuleSheafTensor.hom_ext
  intro U m l
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, comm_hom_pure,
    map_pure, Hom.id_app, ConcreteCategory.id_apply]

/-- Cancel the fixed left line factor from the given tensor isomorphism. -/
def cancelLeftLineIso (hL : LocallyFreeRankOne L)
    (e : tensor L M ≅ tensor L N) : M ≅ N :=
  (lineTensorEquivalence hL).fullyFaithfulFunctor.preimageIso
    (comm M L ≪≫ e ≪≫ (comm N L).symm)

/-- Restoring the cancelled factor recovers the entire original homomorphism. -/
lemma cancelLeftLineIso_hom (hL : LocallyFreeRankOne L)
    (e : tensor L M ≅ tensor L N) :
    map (𝟙 L) (cancelLeftLineIso hL e).hom = e.hom := by
  apply (cancel_epi (comm M L).hom).mp
  rw [tensor_comm_map]
  have h := (lineTensorEquivalence hL).fullyFaithfulFunctor.map_preimage
    (comm M L ≪≫ e ≪≫ (comm N L).symm).hom
  change map (cancelLeftLineIso hL e).hom (𝟙 L) =
    (comm M L).hom ≫ e.hom ≫ (comm N L).inv at h
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Tensor cancellation retains the original isomorphism, including its inverse. -/
lemma congr_cancelLeftLineIso (hL : LocallyFreeRankOne L)
    (e : tensor L M ≅ tensor L N) :
    congr (Iso.refl L) (cancelLeftLineIso hL e) = e := by
  apply Iso.ext
  exact cancelLeftLineIso_hom hL e

end FLT.Mazur.FCurve
