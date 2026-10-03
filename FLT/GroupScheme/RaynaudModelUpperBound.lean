/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudIntegralCoordinates

/-!
# Upper bounds for identified integral models

The schematic graph closure dominates two finite flat models with the same
generic fibre. This is Raynaud 2.2.2's upper-bound construction, before any
small-ramification or presentation argument.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- Invert a bijective generic Galois map, preserving its equivariance. -/
def GenericGaloisHom.inverse {X Y : FF R K} (f : GenericGaloisHom X Y)
    (hf : Function.Bijective f) : GenericGaloisHom Y X := by
  let e := AddEquiv.ofBijective f.toAddMonoidHom hf
  refine { e.symm.toAddMonoidHom with map_smul' := fun σ y ↦ ?_ }
  apply hf.1
  change e (e.symm (σ • y)) = f (σ • e.symm y)
  rw [e.apply_symm_apply, map_smul]
  exact congrArg (σ • ·) (e.apply_symm_apply y).symm

/-- The inverse recovers each original point. -/
@[simp] theorem GenericGaloisHom.inverse_apply {X Y : FF R K} (f : GenericGaloisHom X Y)
    (hf : Function.Bijective f) (x : X.Points) : f.inverse hf (f x) = x :=
  (AddEquiv.ofBijective f.toAddMonoidHom hf).symm_apply_apply x

variable [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]

/-- Construct an upper model and both integral projections, with their prescribed
identifications in one fixed generic fibre. -/
theorem exists_common_model_coordinate_upper_bound {X Y Z : FF R K}
    (f : GenericGaloisHom X Y) (hf : Function.Bijective f)
    (g : GenericGaloisHom X Z) :
    ∃ (W : FF R K) (k : GenericGaloisHom X W), Function.Bijective k ∧
      (∃ a : ModelHom W Y, (genericHom a).comp k = f) ∧
      (∃ b : ModelHom W Z, (genericHom b).comp k = g) ∧
      f.integralCoordinateImage ≤ k.integralCoordinateImage ∧
      g.integralCoordinateImage ≤ k.integralCoordinateImage := by
  let h : GenericGaloisHom Y Z := g.comp (f.inverse hf)
  let k : GenericGaloisHom X h.graphClosure := f
  have ha : (genericHom h.graphFst).comp k = f := by ext x; simp [k]
  have hb : (genericHom h.graphSnd).comp k = g := by ext x; simp [k, h]
  exact ⟨h.graphClosure, k, hf, ⟨h.graphFst, ha⟩, ⟨h.graphSnd, hb⟩,
    f.integralCoordinateImage_le_of_modelHom k h.graphFst ha,
    g.integralCoordinateImage_le_of_modelHom k h.graphSnd hb⟩

end ThreeAdicPlan
