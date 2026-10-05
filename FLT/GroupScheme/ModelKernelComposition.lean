/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsor
public import FLT.GroupScheme.RaynaudModelArithmetic

/-! # Integral kernel containment implies the original zero composite -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {A X Q : FF R K}

/-- The actual augmentation equations imply that the original integral composite is zero. -/
theorem ModelHom.comp_eq_zero_of_augmentation_le (i : ModelHom A X) (q : ModelHom X Q)
    (h : HopfAlgebra.augmentationIdeal q ≤ RingHom.ker i.toAlgHom.toRingHom) :
    i.comp q = ModelHom.zero A Q := by
  ext a
  let ε := Bialgebra.counitAlgHom R Q.CoordinateRing
  have ha : a - algebraMap R Q.CoordinateRing (ε a) ∈ RingHom.ker ε.toRingHom := by
    change ε (a - algebraMap R Q.CoordinateRing (ε a)) = 0
    simp only [map_sub, ε.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have he := h (Ideal.mem_map_of_mem q.toAlgHom.toRingHom ha)
  change (i.comp q).toAlgHom (a - algebraMap R Q.CoordinateRing (ε a)) = 0 at he
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at he
  exact he
end ThreeAdicPlan
