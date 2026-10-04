/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.AugmentationFiberRank
public import FLT.GroupScheme.PDivisibleSystem

/-! # Multiplicativity of coordinate ranks in an actual local kernel sequence -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  {A X Q : FF R K}

/-- A faithfully flat quotient with local coordinates and the actual kernel
presentation gives the product formula for integral coordinate ranks. -/
theorem coordinate_finrank_of_local_kernel [IsLocalRing Q.CoordinateRing]
    (i : ModelHom A X) (q : ModelHom X Q) (hi : Function.Surjective i)
    (hq : q.toAlgHom.toRingHom.FaithfullyFlat)
    (hk : HopfAlgebra.augmentationIdeal q = RingHom.ker i.toAlgHom.toRingHom) :
    Module.finrank R X.CoordinateRing =
      Module.finrank R A.CoordinateRing * Module.finrank R Q.CoordinateRing := by
  let : Algebra Q.CoordinateRing X.CoordinateRing := q.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R Q.CoordinateRing X.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq' q.toAlgHom.comp_algebraMap.symm
  let : Module.FaithfullyFlat Q.CoordinateRing X.CoordinateRing := hq
  let : Module.Finite Q.CoordinateRing X.CoordinateRing :=
    Module.Finite.of_restrictScalars_finite R _ _
  let : Module.Free Q.CoordinateRing X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  let : Module.Free R Q.CoordinateRing := Module.free_of_flat_of_isLocalRing
  have hR : Nontrivial R := (algebraMap R K).domain_nontrivial
  let e : (X.CoordinateRing ⧸ RingHom.ker i.toAlgHom.toRingHom) ≃ₐ[R] A.CoordinateRing :=
    Ideal.quotientKerAlgEquivOfSurjective hi
  have hr := (Bialgebra.counitAlgHom R Q.CoordinateRing).quotient_map_ker_finrank
    (A := X.CoordinateRing)
  change Module.finrank R (X.CoordinateRing ⧸ HopfAlgebra.augmentationIdeal q) = _ at hr
  rw [hk, e.toLinearEquiv.finrank_eq] at hr
  rw [← Module.finrank_mul_finrank R Q.CoordinateRing X.CoordinateRing, ← hr, mul_comm]
end ThreeAdicPlan
