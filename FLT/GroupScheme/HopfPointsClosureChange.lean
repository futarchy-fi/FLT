/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat

/-!
# Changing the value field of Hopf points

Postcomposition preserves the actual convolution group law and intertwines
Galois actions by conjugation through the prescribed algebra equivalence.
-/

@[expose] public noncomputable section

namespace GaloisModule

variable {K Ω Ω' A : Type} [Field K] [Field Ω] [Field Ω']
  [Algebra K Ω] [Algebra K Ω'] [CommRing A] [HopfAlgebra K A]

/-- Postcomposition changes the value field without changing the Hopf algebra. -/
def hopfPointsClosureEquiv (e : Ω ≃ₐ[K] Ω') :
    Additive (A →ₐ[K] Ω) ≃+ Additive (A →ₐ[K] Ω') where
  toFun f := e.toAlgHom.comp f
  invFun f := e.symm.toAlgHom.comp f
  left_inv f := by
    apply AlgHom.ext
    intro x
    exact e.symm_apply_apply (f x)
  right_inv f := by
    apply AlgHom.ext
    intro x
    exact e.apply_symm_apply (f x)
  map_add' f g := by
    apply AlgHom.ext
    intro x
    change e (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _) (Coalgebra.comul x)) =
      Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x)
    induction Coalgebra.comul (R := K) x with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => exact e.map_mul (f x) (g y)

/-- The same original automorphism acts after conjugation. -/
theorem hopfPointsClosureEquiv_smul (e : Ω ≃ₐ[K] Ω') (σ : Ω ≃ₐ[K] Ω)
    (f : Additive (A →ₐ[K] Ω)) :
    hopfPointsClosureEquiv e (σ • f) =
      AlgEquiv.autCongr e σ • hopfPointsClosureEquiv e f := by
  apply AlgHom.ext
  intro x
  change e (σ (f x)) = e (σ (e.symm (e (f x))))
  rw [e.symm_apply_apply]

end GaloisModule
