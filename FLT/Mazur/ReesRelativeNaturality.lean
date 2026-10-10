/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReesAlgebraBaseChange
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Naturality of the relative Rees quotient

The surjections from relative Rees algebras to the actual extended-ideal
Rees algebras commute with chart scalar changes. Thus the affine closed
models use compatible quotient maps on overlaps.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace FLT.Mazur.Rees

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] (I : Ideal R) (f : S →ₐ[R] T)

/-- Scalar extension carries the actual extended ideal to the next extended ideal. -/
lemma extendedIdeal_map :
    (I.map (Algebra.algebraMap R S)).map f.toRingHom =
      I.map (Algebra.algebraMap R T) := by
  rw [Ideal.map_map]
  exact congrArg (fun k : R →+* T ↦ I.map k) f.comp_algebraMap

/-- The actual extended Rees algebra map for a change of chart. -/
def extendedAlgebraMap : reesAlgebra (I.map (Algebra.algebraMap R S)) →+*
    reesAlgebra (I.map (Algebra.algebraMap R T)) :=
  algebraMap _ _ f.toRingHom (extendedIdeal_map I f).le

/-- The relative Rees ring map changes only the chart factor of the tensor product. -/
def relativeAlgebraMap : S ⊗[R] reesAlgebra I →ₐ[R] T ⊗[R] reesAlgebra I :=
  Algebra.TensorProduct.map f (AlgHom.id R _)

/-- Pure tensors retain the base Rees coordinate. -/
lemma relativeAlgebraMap_tmul (s : S) (p : reesAlgebra I) :
    relativeAlgebraMap I f (s ⊗ₜ[R] p) = f s ⊗ₜ[R] p := rfl

/-- The extended Rees map sends each coefficient by the original chart homomorphism. -/
lemma extendedAlgebraMap_coeff (p : reesAlgebra (I.map (Algebra.algebraMap R S)))
    (n : ℕ) : (extendedAlgebraMap I f p).val.coeff n = f (p.val.coeff n) :=
  algebraMap_coeff _ _ _ _ p n

/-- The relative quotient on pure tensors has its original coefficient formula. -/
lemma relativeMap_tmul_coeff (s : S) (p : reesAlgebra I) (n : ℕ) :
    (relativeMap I (s ⊗ₜ[R] p)).val.coeff n =
      s * Algebra.algebraMap R S (p.val.coeff n) := by
  rw [relativeMap_tmul]
  change (s • (baseChangeMap I p).val).coeff n = _
  rw [Polynomial.coeff_smul]
  exact congrArg (s * ·) (algebraMap_coeff I _ (Algebra.algebraMap R S) le_rfl p n)

/-- Relative quotient maps commute with arbitrary base-algebra homomorphisms. -/
lemma relativeMap_naturality (p : S ⊗[R] reesAlgebra I) :
    extendedAlgebraMap I f (relativeMap I p) =
      relativeMap I (relativeAlgebraMap I f p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul s p =>
    apply Subtype.ext
    ext n
    rw [extendedAlgebraMap_coeff, relativeAlgebraMap_tmul,
      relativeMap_tmul_coeff, relativeMap_tmul_coeff, map_mul, f.commutes]

/-- The relative tensor maps preserve identity. -/
lemma relativeAlgebraMap_id : relativeAlgebraMap I (AlgHom.id R S) = AlgHom.id R _ := by
  ext s <;> simp [relativeAlgebraMap]

/-- The relative tensor maps preserve composition. -/
lemma relativeAlgebraMap_comp {U : Type*} [CommRing U] [Algebra R U] (g : T →ₐ[R] U) :
    (relativeAlgebraMap I g).comp (relativeAlgebraMap I f) =
      relativeAlgebraMap I (g.comp f) := by
  ext s <;> simp [relativeAlgebraMap]

end FLT.Mazur.Rees
