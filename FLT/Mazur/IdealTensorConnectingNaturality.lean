/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorConnectingEquiv
public import FLT.Mazur.IdealTensorCoefficientTransition

/-!
# Naturality of the ideal tensor connecting map across ring changes

Compatible semilinear maps of presentations transport the explicit lifts
defining the connecting map. Thus the actual ideal obstruction comparison
agrees with the comparison of reduced presentation relations.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorConnectingNaturality
open IdealTensorConnectingMap IdealTensorCoefficientTransition
variable {R R' P N M P' N' M' : Type*} [CommRing R] [CommRing R']
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M] [Module.Flat R N]
  [AddCommGroup P'] [Module R' P'] [AddCommGroup N'] [Module R' N']
  [AddCommGroup M'] [Module R' M'] [Module.Flat R' N']
  (r : R →+* R') (I : Ideal R)
  (f : P →ₗ[R] N) (q : N →ₗ[R] M)
  (f' : P' →ₗ[R'] N') (q' : N' →ₗ[R'] M')
  (he : Function.Exact f q) (hq : Function.Surjective q)
  (he' : Function.Exact f' q') (hq' : Function.Surjective q')
  (a : P →ₛₗ[r] P') (b : N →ₛₗ[r] N') (c : M →ₛₗ[r] M')
  (hf : ∀ x, f' (a x) = b (f x)) (hc : ∀ x, q' (b x) = c (q x))

omit [Module.Flat R N] [Module.Flat R' N'] in
include hf in
/-- The quotient-coefficient transition sends every original relation into the new kernel. -/
theorem relation_mem_kernel (z : (f.lTensor (R ⧸ I)).ker) :
    f'.lTensor (R' ⧸ I.map r) (TensorProduct.map (quotientTransition r I) a z.val) = 0 := by
  rw [differential_naturality r f f' (quotientTransition r I) a b hf,
    z.property, map_zero]

include hc in
/-- The canonical connecting homomorphisms commute with the actual semilinear transition. -/
theorem connecting_naturality (z : (f.lTensor (R ⧸ I)).ker) :
    (connecting f' q' he' hq' (I.map r)
      ⟨TensorProduct.map (quotientTransition r I) a z.val,
        relation_mem_kernel r I f f' a b hf z⟩).val =
      TensorProduct.map (IdealTensorKernel.idealTransition r I) c
        (connecting f q he hq I z).val := by
  let u := (lifts f q he hq I z).1
  let t := (lifts f q he hq I z).2
  have hu : I.mkQ.rTensor P u = z.val := (lifts_spec f q he hq I z).1
  have ht : f.lTensor R u = I.subtype.rTensor N t :=
    (lifts_spec f q he hq I z).2.1.symm
  have hqmap := differential_naturality r q q'
    (IdealTensorKernel.idealTransition r I) b c hc t
  refine (connecting_eq f' q' he' hq' (I.map r) _
    (TensorProduct.map r.toSemilinearMap a u)
    (TensorProduct.map (IdealTensorKernel.idealTransition r I) b t) ?_ ?_).trans ?_
  · rw [quotient_naturality, hu]
  · rw [differential_naturality r f f' r.toSemilinearMap a b hf, ht,
      inclusion_naturality]
  · exact hqmap

end FLT.Mazur.IdealTensorConnectingNaturality
