/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LinearCokernelSplitCertificate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Uniform flatness certificates for finite matrix cokernels

Flatness of a finite module presentation is equivalent to the existence of
one finite matrix satisfying `A * B * A = A`. The equation controls the whole
cokernel, not just finitely many selected relations. An algebra presentation
is not in general a finite module presentation over its base ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.MatrixCokernel
variable {R : Type*} [CommRing R] {m n : Type*} [Fintype n]

section
variable [Finite m]

/-- The cokernel of a finite matrix is a finitely presented module. -/
theorem finitePresentation (A : Matrix m n R) :
    Module.FinitePresentation R ((m → R) ⧸ LinearMap.range A.mulVecLin) := by
  apply Module.finitePresentation_of_surjective (LinearMap.range A.mulVecLin).mkQ
    (LinearMap.range A.mulVecLin).mkQ_surjective
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_range A.mulVecLin

end

variable [Fintype m]

/-- A finite matrix inner inverse proves flatness of every relation in the cokernel. -/
theorem flat_of_innerInverse (A : Matrix m n R) (B : Matrix n m R)
    (h : A * B * A = A) :
    Module.Flat R ((m → R) ⧸ LinearMap.range A.mulVecLin) := by
  let _ := LinearCokernel.projective_of_innerInverse A.mulVecLin B.mulVecLin
    (by simpa only [Matrix.mulVecLin_mul] using congrArg Matrix.mulVecLin h)
  infer_instance

/-- Flatness produces a finite certificate for the entire presentation. -/
theorem exists_innerInverse_of_flat (A : Matrix m n R)
    [Module.Flat R ((m → R) ⧸ LinearMap.range A.mulVecLin)] :
    ∃ B : Matrix n m R, A * B * A = A := by
  classical
  let _ := finitePresentation A
  let _ := Module.Flat.projective_of_finitePresentation
    (R := R) (M := (m → R) ⧸ LinearMap.range A.mulVecLin)
  obtain ⟨g, hg⟩ := LinearCokernel.exists_innerInverse_of_projective A.mulVecLin
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  change (A * LinearMap.toMatrix' g * A).mulVecLin = A.mulVecLin
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul,
    show (LinearMap.toMatrix' g).mulVecLin = g from Matrix.toLin'_toMatrix' g]
  exact hg

/-- This finite existential equation is equivalent to flatness, uniformly over the ring. -/
theorem flat_iff_innerInverse (A : Matrix m n R) :
    Module.Flat R ((m → R) ⧸ LinearMap.range A.mulVecLin) ↔
      ∃ B : Matrix n m R, A * B * A = A := by
  constructor
  · intro h
    let _ := h
    exact exists_innerInverse_of_flat A
  · rintro ⟨B, hB⟩
    exact flat_of_innerInverse A B hB

end FLT.Mazur.MatrixCokernel
