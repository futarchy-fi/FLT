/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GaloisIntegralCoordinates
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.IsGaloisGroup.Defs

/-!
# Integral descent from a faithful residue action

Distinct residue characters are linearly independent. Selecting a basis of
evaluation vectors gives a matrix with nonzero residue determinant, hence a
unit integral determinant. This removes the coordinate hypothesis from
local integral descent when inertia is trivial.
-/

@[expose] public noncomputable section
open scoped BigOperators TensorProduct
open Module IsLocalRing
namespace SemilinearDescent

universe u
variable {R S : Type u} {G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing S] [Group G] [Fintype G]
  (σ : G →* (S ≃ₐ[R] S))
  (hfaith : Function.Injective (fun g ↦ (residue S).comp (σ g).toRingHom))

open scoped Classical in
include hfaith in
/-- Faithful residue action supplies integral Galois evaluation coordinates. -/
theorem exists_integral_coordinates : ∃ b : G → S, IsUnit (evaluationMatrix σ b).det := by
  classical
  let k := ResidueField S
  let f : G → S →* k := fun g ↦ ((residue S).comp (σ g).toRingHom).toMonoidHom
  have hf : Function.Injective f := fun _ _ h ↦ hfaith (RingHom.toMonoidHom_injective h)
  have hli := (linearIndependent_monoidHom S k).comp f hf
  have hspan : Submodule.span k (Set.range fun s (g : G) ↦ residue S (σ g s)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hli
  let e := Basis.ofSpan hspan.ge
  let e' : Basis G k (G → k) := e.reindex (e.indexEquiv (Pi.basisFun k G))
  have he (i : G) : ∃ s : S, (fun g ↦ residue S (σ g s)) = e' i := by
    apply Basis.ofSpan_subset hspan.ge
    exact ⟨(e.indexEquiv (Pi.basisFun k G)).symm i, (e.reindex_apply _ i).symm⟩
  choose b hb using he
  refine ⟨b, (residue_ne_zero_iff_isUnit _).mp ?_⟩
  rw [RingHom.map_det]
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  convert e'.linearIndependent using 1
  ext i g
  exact congrFun (hb i) g

variable (hinj : Function.Injective (algebraMap R S))
  (hfixed : ∀ s : S, (∀ g, σ g s = s) → ∃ r, algebraMap R S r = s)
  {B : Type u} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (ρ : G →* (B ≃ₐ[R] B))
  (hρ : ∀ g s, ρ g (algebraMap S B s) = algebraMap S B (σ g s))

omit [Fintype G] in
include hfaith hinj hfixed hρ in
/-- Trivial inertia and fixed base scalars imply effective integral algebra descent. -/
theorem residue_recoveryMap_bijective [Finite G] :
    Function.Bijective (recoveryMap (S := S) ρ) := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨b, hb⟩ := exists_integral_coordinates σ hfaith
  exact integral_recoveryMap_bijective σ hinj hfixed ρ hρ b hb

section Inertia

variable {A D Γ : Type u} [CommRing A] [CommRing D] [Algebra A D]
  [IsLocalRing D] [Group Γ] [MulSemiringAction Γ D] [SMulCommClass Γ A D]

/-- Trivial integral inertia makes the residue evaluation characters distinct. -/
theorem residue_characters_injective
    (hI : (maximalIdeal D).inertia Γ = ⊥) :
    Function.Injective (fun g ↦ (residue D).comp
      (MulSemiringAction.toAlgAut Γ A D g).toRingHom) := by
  intro g h he
  apply mul_inv_eq_one.mp
  have hm : g * h⁻¹ ∈ (maximalIdeal D).inertia Γ := by
    rw [Ideal.mem_inertia]
    intro x
    apply (residue_eq_zero_iff _).mp
    rw [map_sub, sub_eq_zero]
    have hx := RingHom.congr_fun he (h⁻¹ • x)
    change residue D (g • (h⁻¹ • x)) = residue D (h • (h⁻¹ • x)) at hx
    simpa only [mul_smul, smul_inv_smul] using hx
  simpa only [hI, Subgroup.mem_bot] using hm

variable [Finite Γ] [IsGaloisGroup Γ A D] [FaithfulSMul A D]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra D C] [IsScalarTower A D C]
  (τ : Γ →* (C ≃ₐ[A] C))
  (hτ : ∀ g s, τ g (algebraMap D C s) = algebraMap D C (g • s))

include hτ in
/-- Integral Galois descent over a local ring with trivial inertia. -/
theorem unramified_recoveryMap_bijective
    (hI : (maximalIdeal D).inertia Γ = ⊥) :
    Function.Bijective (recoveryMap (S := D) τ) := by
  exact residue_recoveryMap_bijective (MulSemiringAction.toAlgAut Γ A D)
    (residue_characters_injective hI) (FaithfulSMul.algebraMap_injective A D)
    (fun s hs ↦ Algebra.IsInvariant.isInvariant s hs) τ hτ

end Inertia

end SemilinearDescent
