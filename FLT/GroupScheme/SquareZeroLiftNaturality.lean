/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SquareZeroPointLift

/-! # Naturality of the canonical infinitesimal multiplication lift -/

@[expose] public noncomputable section
open WithConv
namespace HopfAlgebra
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Bialgebra R A] [Coalgebra.IsCocomm R A] [Algebra R B] [Algebra R C]
  [Module.Projective R A]
  (q : B →ₐ[R] C) (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
  (N : ℕ) (hN : ∀ b ∈ RingHom.ker q, N • b = 0) (x : A →ₐ[R] C)

/-- Canonical lifting commutes with the actual source bialgebra morphism. -/
theorem squareZeroPointLift_precomp {D : Type*} [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] [Module.Projective R D] (h : D →ₐc[R] A) :
    (squareZeroPointLift q hq hJ N hN x).comp h.toAlgHom =
      squareZeroPointLift q hq hJ N hN (x.comp h.toAlgHom) := by
  obtain ⟨f, hf⟩ := Module.projective_lifting_property q.toLinearMap x.toLinearMap hq
  have hf' : q.toLinearMap.comp (f.comp h.toLinearMap) =
      (x.comp h.toAlgHom).toLinearMap := by
    rw [← LinearMap.comp_assoc, hf]
    rfl
  apply AlgHom.toLinearMap_injective
  rw [AlgHom.comp_toLinearMap, squareZeroPointLift_eq_convPow q hq hJ N hN x f hf,
    squareZeroPointLift_eq_convPow q hq hJ N hN (x.comp h.toAlgHom) _ hf']
  exact linear_convPow_comp_bialgHom h f N

/-- A commuting map of square-zero thickenings preserves the canonical point itself. -/
theorem squareZeroPointLift_postcomp {D E : Type*} [CommRing D] [CommRing E]
    [Algebra R D] [Algebra R E] (q' : D →ₐ[R] E) (hq' : Function.Surjective q')
    (hJ' : RingHom.ker q' ^ 2 = ⊥) (hN' : ∀ d ∈ RingHom.ker q', N • d = 0)
    (β : B →ₐ[R] D) (γ : C →ₐ[R] E) (hc : q'.comp β = γ.comp q) :
    β.comp (squareZeroPointLift q hq hJ N hN x) =
      squareZeroPointLift q' hq' hJ' N hN' (γ.comp x) := by
  obtain ⟨f, hf⟩ := Module.projective_lifting_property q.toLinearMap x.toLinearMap hq
  have hf' : q'.toLinearMap.comp (β.toLinearMap.comp f) = (γ.comp x).toLinearMap := by
    ext a
    change q' (β (f a)) = γ (x a)
    rw [show q' (β (f a)) = γ (q (f a)) from AlgHom.congr_fun hc (f a),
      show q (f a) = x a from LinearMap.congr_fun hf a]
  apply AlgHom.toLinearMap_injective
  rw [AlgHom.comp_toLinearMap, squareZeroPointLift_eq_convPow q hq hJ N hN x f hf,
    squareZeroPointLift_eq_convPow q' hq' hJ' N hN' (γ.comp x) _ hf']
  exact algHom_comp_linear_convPow β f N

end HopfAlgebra
