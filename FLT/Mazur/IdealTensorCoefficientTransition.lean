/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorTransition
public import FLT.Mazur.TensorKernelExtension

/-!
# Changing the ideal coefficient sequence across a ring map

The ideal, ring, and quotient transition maps form an actual commuting
diagram. Semilinear tensor naturality keeps these maps compatible with
presentation differentials when both the ring and module change.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorCoefficientTransition
variable {R R' : Type*} [CommRing R] [CommRing R'] (r : R →+* R') (I : Ideal R)

/-- The quotient coefficient transition is semilinear over the original ring map. -/
def quotientTransition : (R ⧸ I) →ₛₗ[r] R' ⧸ I.map r where
  toFun := Ideal.quotientMap (I.map r) r Ideal.le_comap_map
  map_add' := map_add _
  map_smul' a x := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (I.map r) (r (a * b)) =
      Ideal.Quotient.mk (I.map r) (r a * r b)
    rw [map_mul]

@[simp]
theorem quotientTransition_mk (a : R) :
    quotientTransition r I (Ideal.Quotient.mk I a) = Ideal.Quotient.mk (I.map r) (r a) :=
  rfl

variable {P N P' N' C C' : Type*}
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup P'] [Module R' P'] [AddCommGroup N'] [Module R' N']
  [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R' C']

/-- Changing both coefficients and modules commutes with the presentation differential. -/
theorem differential_naturality (f : P →ₗ[R] N) (f' : P' →ₗ[R'] N')
    (a : C →ₛₗ[r] C') (b : P →ₛₗ[r] P') (c : N →ₛₗ[r] N')
    (h : ∀ x, f' (b x) = c (f x)) (z : C ⊗[R] P) :
    f'.lTensor C' (TensorProduct.map a b z) =
      TensorProduct.map a c (f.lTensor C z) := by
  induction z with
  | tmul x y => simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Changing modules and coefficients also commutes with a coefficient differential. -/
theorem coefficient_naturality (g : P →ₗ[R] N) (g' : P' →ₗ[R'] N')
    (a : P →ₛₗ[r] P') (b : N →ₛₗ[r] N') (c : C →ₛₗ[r] C')
    (h : ∀ x, g' (a x) = b (g x)) (z : P ⊗[R] C) :
    g'.rTensor C' (TensorProduct.map a c z) =
      TensorProduct.map b c (g.rTensor C z) := by
  induction z with
  | tmul x y => simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The ideal transition respects its actual inclusion into the base ring. -/
theorem inclusion_naturality (c : C →ₛₗ[r] C') (z : I ⊗[R] C) :
    (I.map r).subtype.rTensor C' (TensorProduct.map (IdealTensorKernel.idealTransition r I) c z) =
      TensorProduct.map r.toSemilinearMap c (I.subtype.rTensor C z) :=
  coefficient_naturality r I.subtype (I.map r).subtype
    (IdealTensorKernel.idealTransition r I) r.toSemilinearMap c (fun _ ↦ rfl) z

/-- The quotient transition respects the quotient map of the extended ideal. -/
theorem quotient_naturality (c : C →ₛₗ[r] C') (z : R ⊗[R] C) :
    (I.map r).mkQ.rTensor C' (TensorProduct.map r.toSemilinearMap c z) =
      TensorProduct.map (quotientTransition r I) c (I.mkQ.rTensor C z) :=
  coefficient_naturality r I.mkQ (I.map r).mkQ
    r.toSemilinearMap (quotientTransition r I) c (fun _ ↦ rfl) z

end FLT.Mazur.IdealTensorCoefficientTransition
