/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarOrbitBalancingIdeal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finite original scalar equations for free orbit comparisons

Generators of the fixed algebra give generators of the exact comparison
kernel. This constructs finite equations when that algebra is finite type;
it does not infer finiteness of any separate correction cokernel.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarOrbitTensorComparison
open FiniteGroupQuotient
variable (G R A : Type*) [Group G] [CommRing R] [CommRing A]
  [MulSemiringAction G A] [Algebra R A] [Algebra R (invariantRing G A)]
  [IsScalarTower R (invariantRing G A) A]
local notation "S" => invariantRing G A
local notation "C" => A ⊗[R] A

/-- Algebra generators suffice for the full ideal, not just its zero locus. -/
theorem balancingIdeal_eq_span (s : Set S) (hs : Algebra.adjoin R s = ⊤) :
    balancingIdeal G R A = Ideal.span
      ((fun a : S ↦ (a.val ⊗ₜ[R] (1 : A)) - (1 ⊗ₜ[R] a.val)) '' s) := by
  let I : Ideal C := Ideal.span
    ((fun a : S ↦ (a.val ⊗ₜ[R] (1 : A)) - (1 ⊗ₜ[R] a.val)) '' s)
  let l : S →ₐ[R] C ⧸ I := (Ideal.Quotient.mkₐ R I).comp
    (Algebra.TensorProduct.includeLeft.comp (IsScalarTower.toAlgHom R S A))
  let r : S →ₐ[R] C ⧸ I := (Ideal.Quotient.mkₐ R I).comp
    (Algebra.TensorProduct.includeRight.comp (IsScalarTower.toAlgHom R S A))
  have h : l = r := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro a ha
    apply Ideal.Quotient.eq.mpr
    exact Ideal.subset_span (Set.mem_image_of_mem _ ha)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact Ideal.Quotient.eq.mp (DFunLike.congr_fun h a)
  · apply Ideal.span_mono
    exact Set.image_subset_range _ _

/-- Finite type of the full fixed algebra constructs finite original comparison equations. -/
theorem balancingIdeal_fg [Algebra.FiniteType R S] : (balancingIdeal G R A).FG := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  rw [balancingIdeal_eq_span G R A (s : Set S) hs]
  exact Submodule.fg_def.mpr
    ⟨_, s.finite_toSet.image _, rfl⟩

variable [Finite G] (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)
include hfree

/-- The finite equation system cuts out the actual original orbit comparison. -/
theorem comparison_ker_fg [Algebra.FiniteType R S] :
    (RingHom.ker (comparison G R A).toRingHom).FG := by
  rw [comparison_ker_eq_balancingIdeal G R A hfree]
  exact balancingIdeal_fg G R A

end FLT.Mazur.ScalarOrbitTensorComparison
