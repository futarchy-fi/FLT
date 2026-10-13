/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeTranslationNorm

/-!
# Naturality of translation norms in the source coefficients

The translation algebra has a genuine finite basis over the ground ring.
The source coefficient map can be arbitrary. Naturality is proved for every
tensor coefficient, not only coefficients coming from the translation ring.
-/

@[expose] public noncomputable section
open Module TensorProduct
namespace FLT.Mazur.FiniteFreeTranslationNorm
universe u v w
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type w} (b : Basis ι R S)
  {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (f : B →ₐ[R] C)

/-- Base-changed coordinates respect the actual source algebra map. -/
theorem repr_tensor_map (x : B ⊗[R] S) (i : ι) :
    (b.baseChange C).repr ((Algebra.TensorProduct.map f (AlgHom.id R S)) x) i =
      f ((b.baseChange B).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a s =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Basis.baseChange_repr_tmul, map_smul]
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

/-- Multiplication matrices commute with a possibly noninjective source coefficient map. -/
theorem leftMulMatrix_tensor_map [Fintype ι] [DecidableEq ι] (x : B ⊗[R] S) :
    Algebra.leftMulMatrix (b.baseChange C) (Algebra.TensorProduct.map f (AlgHom.id R S) x) =
      f.toRingHom.mapMatrix (Algebra.leftMulMatrix (b.baseChange B) x) := by
  ext i j
  simp only [Algebra.leftMulMatrix_eq_repr_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hj : (Algebra.TensorProduct.map f (AlgHom.id R S)) (b.baseChange B j) =
      b.baseChange C j := by
    simp only [Basis.baseChange_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rw [← hj, ← map_mul, repr_tensor_map]
  rfl

variable [Finite ι]
include b

/-- Full tensor norms commute with arbitrary maps of the source algebra. -/
theorem norm_tensor_map (x : B ⊗[R] S) :
    Algebra.norm C (Algebra.TensorProduct.map f (AlgHom.id R S) x) =
      f (Algebra.norm B x) := by
  classical
  let _ := Fintype.ofFinite ι
  rw [Algebra.norm_eq_matrix_det (b.baseChange C),
    Algebra.norm_eq_matrix_det (b.baseChange B), leftMulMatrix_tensor_map]
  exact (RingHom.map_det f.toRingHom _).symm

/-- Isomorphic transported envelopes give the same norm in the new source coefficients. -/
theorem norm_tensor_map_equiv {D : Type*} [CommRing D] [Algebra C D]
    (e : (C ⊗[R] S) ≃ₐ[C] D) (x : B ⊗[R] S) :
    Algebra.norm C (e (Algebra.TensorProduct.map f (AlgHom.id R S) x)) =
      f (Algebra.norm B x) := by
  rw [Algebra.norm_eq_of_algEquiv, norm_tensor_map b f]

/-- An actual envelope transport identifies the two endpoint norms. -/
theorem norm_eq_of_transport (g : B →ₐ[R] C) (e : (C ⊗[R] S) ≃ₐ[C] (C ⊗[R] S))
    (x : B ⊗[R] S)
    (hx : e (Algebra.TensorProduct.map f (AlgHom.id R S) x) =
      Algebra.TensorProduct.map g (AlgHom.id R S) x) :
    f (Algebra.norm B x) = g (Algebra.norm B x) := by
  rw [← norm_tensor_map b f, ← Algebra.norm_eq_of_algEquiv e, hx, norm_tensor_map b g]

end FLT.Mazur.FiniteFreeTranslationNorm
