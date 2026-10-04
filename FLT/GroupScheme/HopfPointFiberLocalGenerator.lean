/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPointFiberDifferenceEvaluation
public import FLT.GroupScheme.LocalInvertibleSubmodule

/-!
# Local homogeneous generators and their integral parameters

This isolates the strong-grading obligation: one must prove that one belongs
to the product of opposite homogeneous components. Given that obligation,
invertibility, a unit generator, and its descended power are constructed.
The obligation is not yet proved for an arbitrary multiplicative torsor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace HopfAlgebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra B A] [IsScalarTower R B A]
  [Module.FaithfullyFlat B A]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
  (p : B →ₐ[R] R) (t : (A ⧸ augmentationIdeal f)ˣ)
  (hstrong : (1 : PointFiber (A := A) p) ∈
    pointFiberHomogeneous f hf p (t : A ⧸ augmentationIdeal f) *
      pointFiberHomogeneous f hf p (↑t⁻¹))

/-- Opposite homogeneous components give a unit in the submodule semiring
once the strong-grading obligation is discharged. -/
def pointFiberHomogeneousUnit : (Submodule R (PointFiber (A := A) p))ˣ where
  val := pointFiberHomogeneous f hf p t
  inv := pointFiberHomogeneous f hf p (↑t⁻¹)
  val_inv := (pointFiberHomogeneous_mul_inv_eq_one_iff f hf p t).mpr hstrong
  inv_val := by
    rw [mul_comm]
    exact (pointFiberHomogeneous_mul_inv_eq_one_iff f hf p t).mpr hstrong

include hstrong in
/-- The homogeneous module is invertible under the explicit product obligation. -/
theorem pointFiberHomogeneous_invertible :
    Module.Invertible R (pointFiberHomogeneous f hf p (t : A ⧸ augmentationIdeal f)) :=
  inferInstanceAs (Module.Invertible R
    (pointFiberHomogeneousUnit f hf p t hstrong : Submodule R (PointFiber (A := A) p)))

variable [IsLocalRing R]

/-- Local Picard triviality constructs a homogeneous unit; none is supplied. -/
def pointFiberLocalGenerator : (PointFiber (A := A) p)ˣ :=
  Submodule.localGeneratorUnit (pointFiberHomogeneousUnit f hf p t hstrong)

/-- The constructed unit lies in the desired component. -/
theorem pointFiberLocalGenerator_mem :
    (pointFiberLocalGenerator f hf p t hstrong : PointFiber (A := A) p) ∈
      pointFiberHomogeneous f hf p t := by
  change (Submodule.localGeneratorUnit (pointFiberHomogeneousUnit f hf p t hstrong) :
    PointFiber (A := A) p) ∈ _
  rw [Submodule.coe_localGeneratorUnit]
  exact Submodule.localUnitGenerator_mem (pointFiberHomogeneousUnit f hf p t hstrong)

/-- The constructed unit generates the entire homogeneous component. -/
theorem pointFiberLocalGenerator_span :
    Submodule.span R {(pointFiberLocalGenerator f hf p t hstrong : PointFiber (A := A) p)} =
      pointFiberHomogeneous f hf p t := by
  change Submodule.span R
    {(Submodule.localGeneratorUnit (pointFiberHomogeneousUnit f hf p t hstrong) :
      PointFiber (A := A) p)} =
    (pointFiberHomogeneousUnit f hf p t hstrong : Submodule R (PointFiber (A := A) p))
  rw [Submodule.coe_localGeneratorUnit]
  exact (Submodule.eq_span_localUnitGenerator (pointFiberHomogeneousUnit f hf p t hstrong)).symm

/-- Its torsion power descends uniquely to an integral unit. -/
theorem pointFiberLocalGenerator_parameter (n : ℕ) (ht : t ^ n = 1) :
    ∃! u : Rˣ, Units.map (algebraMap R (PointFiber (A := A) p)).toMonoidHom u =
      pointFiberLocalGenerator f hf p t hstrong ^ n := by
  apply pointFiber_exists_unit_power f hf p n (pointFiberLocalGenerator f hf p t hstrong) t
  · exact congrArg Units.val ht
  · exact pointFiberLocalGenerator_mem f hf p t hstrong

/-- Evaluation of the constructed generator satisfies an integral unit equation. -/
theorem pointFiberLocalGenerator_evaluated_power {C : Type*} [CommRing C] [Algebra R C]
    (x : PointFiber (A := A) p →ₐ[R] C) (n : ℕ) (ht : t ^ n = 1) :
    ∃ u : Rˣ, Units.map x.toMonoidHom (pointFiberLocalGenerator f hf p t hstrong) ^ n =
      Units.map (algebraMap R C).toMonoidHom u := by
  obtain ⟨u, hu, _⟩ := pointFiberLocalGenerator_parameter f hf p t hstrong n ht
  refine ⟨u, ?_⟩
  have h := congrArg (Units.map x.toMonoidHom) hu
  rw [map_pow] at h
  exact h.symm.trans (by apply Units.ext; exact x.commutes (u : R))

/-- The constructed generator evaluates the actual Hopf difference as a root ratio. -/
theorem pointFiberLocalGenerator_difference {C : Type*} [CommRing C] [Algebra R C]
    (x y : PointFiber (A := A) p →ₐ[R] C) :
    Units.map (pointFiberDifferenceEvaluation f hf p x y).toMonoidHom t =
      Units.map y.toMonoidHom (pointFiberLocalGenerator f hf p t hstrong) /
        Units.map x.toMonoidHom (pointFiberLocalGenerator f hf p t hstrong) :=
  pointFiberDifferenceEvaluation_unitRatio f hf p x y _ t
    (pointFiberLocalGenerator_mem f hf p t hstrong)

end HopfAlgebra
