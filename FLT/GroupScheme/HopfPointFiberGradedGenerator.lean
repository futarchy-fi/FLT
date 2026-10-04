/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPointFiberStrongGrading

/-!
# Integral parameters from a multiplicatively graded Hopf fibre

The generator is constructed using the proved strong grading. Its power descends
to an integral unit, and the actual Hopf difference evaluates to its root ratio.
The integral kernel basis remains a prerequisite of this construction.
-/

@[expose] public noncomputable section
namespace HopfAlgebra

variable {R A B G : Type*} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra B A] [IsScalarTower R B A]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
  (p : B →ₐ[R] R) [Group G] [Finite G]
  (b : Module.Basis G R (A ⧸ augmentationIdeal f))
  (hone : b 1 = 1) (hmul : ∀ i j, b (i * j) = b i * b j)
  (hδ : CoactionBasis.diagonal b ∘ₗ (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap =
    TensorProduct.map (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap
      (Ideal.Quotient.mkₐ R (augmentationIdeal f)).toLinearMap ∘ₗ Coalgebra.comul)

/-- The degree units respect the entire group law. -/
def pointFiberDegreeHom : G →* (A ⧸ augmentationIdeal f)ˣ where
  toFun := pointFiberDegreeUnit f b hone hmul
  map_one' := Units.ext hone
  map_mul' i j := Units.ext (hmul i j)

variable [Module.FaithfullyFlat B A] [IsLocalRing R]

/-- A homogeneous generator constructed without a strong-grading premise. -/
def pointFiberGradedGenerator (i : G) : (PointFiber (A := A) p)ˣ :=
  pointFiberLocalGenerator f hf p (pointFiberDegreeUnit f b hone hmul i)
    (pointFiber_degree_strong f hf p b hone hmul hδ i)

/-- The constructed generator has the requested degree. -/
theorem pointFiberGradedGenerator_mem (i : G) :
    (pointFiberGradedGenerator f hf p b hone hmul hδ i : PointFiber (A := A) p) ∈
      pointFiberHomogeneous f hf p (b i) :=
  pointFiberLocalGenerator_mem f hf p _ _

/-- It spans the entire homogeneous component. -/
theorem pointFiberGradedGenerator_span (i : G) :
    Submodule.span R
      {(pointFiberGradedGenerator f hf p b hone hmul hδ i : PointFiber (A := A) p)} =
      pointFiberHomogeneous f hf p (b i) :=
  pointFiberLocalGenerator_span f hf p _ _

/-- A torsion degree gives a unique integral Kummer unit. -/
theorem pointFiberGradedGenerator_parameter (i : G) (n : ℕ) (hi : i ^ n = 1) :
    ∃! u : Rˣ, Units.map (algebraMap R (PointFiber (A := A) p)).toMonoidHom u =
      pointFiberGradedGenerator f hf p b hone hmul hδ i ^ n := by
  apply pointFiberLocalGenerator_parameter f hf p _ _ n
  change pointFiberDegreeHom f b hone hmul i ^ n = 1
  rw [← map_pow, hi, map_one]

/-- The parameter equation survives evaluation at any fibre point. -/
theorem pointFiberGradedGenerator_evaluated_power {C : Type*} [CommRing C] [Algebra R C]
    (x : PointFiber (A := A) p →ₐ[R] C) (i : G) (n : ℕ) (hi : i ^ n = 1) :
    ∃ u : Rˣ, Units.map x.toMonoidHom
      (pointFiberGradedGenerator f hf p b hone hmul hδ i) ^ n =
        Units.map (algebraMap R C).toMonoidHom u := by
  apply pointFiberLocalGenerator_evaluated_power f hf p _ _ x n
  change pointFiberDegreeHom f b hone hmul i ^ n = 1
  rw [← map_pow, hi, map_one]

/-- The actual inverse-torsor difference evaluates to the generator's root ratio. -/
theorem pointFiberGradedGenerator_difference {C : Type*} [CommRing C] [Algebra R C]
    (x y : PointFiber (A := A) p →ₐ[R] C) (i : G) :
    Units.map (pointFiberDifferenceEvaluation f hf p x y).toMonoidHom
      (pointFiberDegreeUnit f b hone hmul i) =
      Units.map y.toMonoidHom (pointFiberGradedGenerator f hf p b hone hmul hδ i) /
        Units.map x.toMonoidHom (pointFiberGradedGenerator f hf p b hone hmul hδ i) :=
  pointFiberLocalGenerator_difference f hf p _ _ x y

end HopfAlgebra
