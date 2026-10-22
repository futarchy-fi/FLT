/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Constructing spanning relation gradients from the differential fiber

For a finite polynomial presentation, vanishing of the differential fiber
forces the gradients of actual kernel relations to span the residue coordinate
space. Tensor right exactness retains the entire presentation kernel; no
reducedness or complete-intersection assumption is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarPresentationResidueGradients
open Algebra MvPolynomial TensorProduct
variable {R A K : Type} [CommRing R] [CommRing A] [CommRing K]
  [Algebra R A] [Algebra A K] {n : ℕ} (P : Generators R A (Fin n))

/-- Coordinates of the base changed conormal map in the polynomial differential basis. -/
def gradientMap :
    K ⊗[A] P.toExtension.Cotangent →ₗ[K] (Fin n → K) :=
  (Finsupp.linearEquivFunOnFinite K K (Fin n)).toLinearMap ∘ₗ
    (P.cotangentSpaceBasis.baseChange K).repr.toLinearMap ∘ₗ
      P.toExtension.cotangentComplex.baseChange K

/-- The conormal class of a genuine equation maps to its gradient, with its coefficient. -/
theorem gradientMap_tmul (a : K) (f : P.ker) (j : Fin n) :
    gradientMap P (a ⊗ₜ[A] Extension.Cotangent.mk (P := P.toExtension) f) j =
      a * algebraMap A K (aeval P.val (pderiv j f.val)) := by
  simp only [gradientMap, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearMap.baseChange_tmul,
    Finsupp.linearEquivFunOnFinite_apply, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_comm]
  congr 2
  change P.cotangentSpaceBasis.repr (1 ⊗ₜ[P.toExtension.Ring]
    KaehlerDifferential.D R P.toExtension.Ring f.val) j = _
  exact P.cotangentSpaceBasis_repr_one_tmul f.val j

attribute [local irreducible] gradientMap

/-- A zero differential fiber makes the base changed conormal map surjective. -/
theorem gradientMap_surjective
    [Subsingleton (K ⊗[A] KaehlerDifferential R A)] :
    Function.Surjective (gradientMap (K := K) P) := by
  have hex := lTensor_exact K
    P.toExtension.exact_cotangentComplex_toKaehler P.toExtension.toKaehler_surjective
  have hs : Function.Surjective (P.toExtension.cotangentComplex.baseChange K) := by
    intro x
    exact (hex x).mp (Subsingleton.elim _ _)
  unfold gradientMap
  exact (Finsupp.linearEquivFunOnFinite K K (Fin n)).surjective.comp
    ((P.cotangentSpaceBasis.baseChange K).repr.surjective.comp hs)

/-- Actual kernel relations span all residue gradients when the differential fiber vanishes. -/
theorem span_eq_top [Subsingleton (K ⊗[A] KaehlerDifferential R A)] :
    Submodule.span K (Set.range fun f : P.ker ↦ fun j ↦
      algebraMap A K (aeval P.val (pderiv j f.val))) = ⊤ := by
  let N := Submodule.span K (Set.range fun f : P.ker ↦ fun j ↦
    algebraMap A K (aeval P.val (pderiv j f.val)))
  have hm (x : K ⊗[A] P.toExtension.Cotangent) : gradientMap P x ∈ N := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact N.add_mem hx hy
    | tmul a f =>
      obtain ⟨f, rfl⟩ := Extension.Cotangent.mk_surjective f
      have he : gradientMap P (a ⊗ₜ[A] Extension.Cotangent.mk (P := P.toExtension) f) =
          a • (fun j ↦ algebraMap A K (aeval P.val (pderiv j f.val))) := by
        ext j
        exact gradientMap_tmul P a f j
      rw [he]
      exact N.smul_mem a (Submodule.subset_span ⟨f, rfl⟩)
  apply top_unique
  intro v _
  obtain ⟨x, rfl⟩ := gradientMap_surjective P v
  exact hm x

end FLT.Mazur.ScalarPresentationResidueGradients
