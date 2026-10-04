/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualPairing
public import FLT.GroupScheme.CartierDualMaps

/-! # Naturality of the actual geometric Cartier pairing -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
variable {K L A B : Type} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [HopfAlgebra K A] [HopfAlgebra K B]
  [Coalgebra.IsCocomm K A] [Coalgebra.IsCocomm K B]
  [Module.Finite K A] [Module.Finite K B]
  [Algebra.Etale K A] [Algebra.Etale K B] [IsSepClosed L]
attribute [local instance] HopfAlgebra.pointsCommGroup

omit [Coalgebra.IsCocomm K A] [Coalgebra.IsCocomm K B] in
/-- Transposing a coordinate map transports the tensor representing a geometric point. -/
theorem geometricPointElement_naturality (f : A →ₐc[K] B) (x : B →ₐ[K] L) :
    Algebra.TensorProduct.map (AlgHom.id L L) (bialgMap f).toAlgHom
      (geometricPointElement K L B x) = geometricPointElement K L A (x.comp f.toAlgHom) := by
  apply (baseChangeAlgEquiv (R := K) (A := A) L).injective
  apply WithConv.ext
  apply (TensorProduct.isBaseChange K A L).algHom_ext
  intro a
  have he (t : L ⊗[K] CartierDual K B) :
      baseChangeAlgEquiv L
        (Algebra.TensorProduct.map (AlgHom.id L L) (bialgMap f).toAlgHom t) (1 ⊗ₜ a) =
      baseChangeAlgEquiv L t (1 ⊗ₜ f a) := by
    induction t using TensorProduct.inductionOn with
    | tmul l φ =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, baseChangeAlgEquiv_tmul]
      rfl
    | add t u ht hu => simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply, ht, hu]
  exact (he _).trans ((geometricPointElement_eval K L B x (f a)).trans
    (geometricPointElement_eval K L A (x.comp f.toAlgHom) a).symm)

/-- Evaluation pairs a transpose with the original coordinate map. -/
theorem geometricCharactersEquiv_naturality (f : A →ₐc[K] B)
    (ψ : CartierDual K A →ₐ[K] L) (x : B →ₐ[K] L) :
    geometricCharactersEquiv K L B (ψ.comp (bialgMap f).toAlgHom) x =
      geometricCharactersEquiv K L A ψ (x.comp f.toAlgHom) := by
  apply Units.ext
  rw [geometricCharactersEquiv_apply, geometricCharactersEquiv_apply,
    ← geometricPointElement_naturality f x]
  generalize geometricPointElement K L B x = t
  induction t using TensorProduct.inductionOn with
  | tmul l φ => rfl
  | add t u ht hu => simp only [map_add, ht, hu]

end HopfAlgebra.CartierDual
