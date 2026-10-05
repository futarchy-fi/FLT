/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ModelAugmentationPoints
public import FLT.GroupScheme.IntegralKernelEquations

/-! # Recovering the actual integral kernel from flatness and generic exactness -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  {A X Q : FF R K}

/-- The integral augmentation equations equal those of the given closed inclusion
when the quotient is flat and its original generic sequence is exact. -/
theorem ModelHom.augmentationIdeal_eq_ker_of_generic_exact
    (i : ModelHom A X) (q : ModelHom X Q)
    (hi : Function.Surjective i) (hip : Function.Injective (genericHom i))
    (hq : q.toAlgHom.toRingHom.Flat)
    (he : ∀ x, genericHom q x = 0 ↔ ∃ a, genericHom i a = x) :
    HopfAlgebra.augmentationIdeal q = RingHom.ker i.toAlgHom.toRingHom := by
  let : Algebra Q.CoordinateRing X.CoordinateRing := q.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R Q.CoordinateRing X.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' q.toAlgHom.comp_algebraMap.symm
  let : Module.Flat Q.CoordinateRing X.CoordinateRing := hq
  let : Module.Flat R (X.CoordinateRing ⧸ HopfAlgebra.augmentationIdeal q) :=
    (Bialgebra.counitAlgHom R Q.CoordinateRing).quotient_map_ker_flat
  rw [i.ker_eq_closureIdeal hip hi]
  ext a
  rw [X.mem_ideal_iff_of_flat_quotient, GenericGaloisHom.mem_closureIdeal_iff_vanish]
  simp only [← q.genericHom_eq_zero_iff_vanish, he]
end ThreeAdicPlan
