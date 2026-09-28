/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalEisensteinPresentation
public import FLT.Mathlib.RingTheory.Unramified.PowerBasis
public import FLT.Mathlib.RingTheory.Polynomial.DistinctRoots

/-!
# The inertia orbit of a relative integral generator

Inertia fixes an unramified coefficient ring pointwise. An integral generator
over that ring therefore has exactly its inertia conjugates as roots.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Polynomial IsLocalRing

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- The inertia subgroup of the integral automorphism group. -/
abbrev ThreeAdicIntegralInertia :=
  (maximalIdeal (ThreeAdicIntegers L)).inertia
    (ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L)

variable {C : Type} [CommRing C] [Algebra ℤ_[3] C]
  [Algebra C (ThreeAdicIntegers L)] [IsScalarTower ℤ_[3] C (ThreeAdicIntegers L)]
  [Algebra.FormallyUnramified ℤ_[3] C]

/-- Inertia fixes every element of an unramified monogenic coefficient ring. -/
theorem threeAdicInertiaFixesCoefficient (pc : PowerBasis ℤ_[3] C)
    (σ : ThreeAdicIntegralInertia L) (c : C) :
    σ.val (algebraMap C (ThreeAdicIntegers L) c) = algebraMap C (ThreeAdicIntegers L) c := by
  let f := IsScalarTower.toAlgHom ℤ_[3] C (ThreeAdicIntegers L)
  have heq : σ.val.toAlgHom.comp f = f := pc.algHomEqOfResidueEq _ _ (by
    have h := (Ideal.mem_inertia.mp σ.property) (f pc.gen)
    exact sub_eq_zero.mp (by simpa using (residue_eq_zero_iff _).mpr h))
  exact congrArg (fun h : C →ₐ[ℤ_[3]] ThreeAdicIntegers L => h c) heq

/-- An integral inertia automorphism is linear over the unramified coefficient ring. -/
def threeAdicInertiaCoefficientAut (pc : PowerBasis ℤ_[3] C)
    (σ : ThreeAdicIntegralInertia L) : ThreeAdicIntegers L ≃ₐ[C] ThreeAdicIntegers L :=
  { σ.val.toRingEquiv with commutes' := threeAdicInertiaFixesCoefficient L pc σ }

/-- Distinct inertia automorphisms have distinct images of a relative integral generator. -/
theorem threeAdicInertiaOrbitInjective (pc : PowerBasis ℤ_[3] C)
    (pb : PowerBasis C (ThreeAdicIntegers L)) :
    Function.Injective (fun σ : ThreeAdicIntegralInertia L => σ.val pb.gen) := by
  intro σ τ h
  have heq := pb.algHom_ext
    (f := (threeAdicInertiaCoefficientAut L pc σ).toAlgHom)
    (g := (threeAdicInertiaCoefficientAut L pc τ).toAlgHom) h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun f : ThreeAdicIntegers L →ₐ[C] ThreeAdicIntegers L => f x) heq

open scoped Classical in
/-- A relative integral generator of degree equal to the ramification index
has minimal polynomial given by the inertia orbit product. -/
theorem threeAdicRelativeMinpolyEqProdInertia [IsGalois ℚ_[3] L] [Nontrivial C]
    (pc : PowerBasis ℤ_[3] C) (pb : PowerBasis C (ThreeAdicIntegers L))
    (hdim : pb.dim = threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)})) :
    (minpoly C pb.gen).map (algebraMap C (ThreeAdicIntegers L)) =
      ∏ σ : ThreeAdicIntegralInertia L, (X - Polynomial.C (σ.val pb.gen)) := by
  apply eqProdOfDistinctRoots _ ((minpoly.monic pb.isIntegral_gen).map _)
    (fun σ : ThreeAdicIntegralInertia L => σ.val pb.gen)
    (threeAdicInertiaOrbitInjective L pc pb)
  · intro σ
    rw [Polynomial.IsRoot, eval_map_algebraMap]
    change aeval ((threeAdicInertiaCoefficientAut L pc σ) pb.gen) (minpoly C pb.gen) = 0
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  · rw [(minpoly.monic pb.isIntegral_gen).natDegree_map, pb.natDegree_minpoly,
      hdim, ← Nat.card_eq_fintype_card, threeAdicInertiaCard]

/-- Inertia displacement is measured by the relative power-basis generator. -/
theorem threeAdicAddValRelativeGenSubInertia (pc : PowerBasis ℤ_[3] C)
    (pb : PowerBasis C (ThreeAdicIntegers L)) (σ : ThreeAdicIntegralInertia L)
    (hσ : σ ≠ 1) :
    IsDiscreteValuationRing.addVal (ThreeAdicIntegers L) (pb.gen - σ.val pb.gen) =
      (threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom) : ℕ∞) := by
  have hid : threeAdicDisplacementIdeal L σ.val.toAlgHom =
      Ideal.span {pb.gen - σ.val pb.gen} :=
    pb.spanSubHomEqSpanGen (threeAdicInertiaCoefficientAut L pc σ).toAlgHom
  rw [hid]
  apply threeAdicAddValEqIdealOrder
  intro h
  exact hσ (threeAdicInertiaOrbitInjective L pc pb (sub_eq_zero.mp h).symm)

/-- Displacement ideal order vanishes outside inertia. -/
theorem threeAdicDisplacementIdealOrderZeroOutsideInertia
    (σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L)
    (hσ : σ ∉ ThreeAdicIntegralInertia L) :
    threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.toAlgHom) = 0 := by
  have h := threeAdicDisplacementOrderEqZeroOfNotInertia L σ hσ
  have he : (threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (threeAdicIdealOrder_three_pos L))
  simp only [threeAdicDisplacementOrder, normalizedIdealOrder, div_eq_zero_iff, he,
    or_false, Nat.cast_eq_zero] at h
  exact h

open scoped Classical in
/-- The different order is the sum of the nonidentity inertia displacements. -/
theorem threeAdicDifferentOrderEqSumInertia [IsGalois ℚ_[3] L] :
    threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) =
      ∑ σ ∈ Finset.univ.erase (1 : ThreeAdicIntegralInertia L),
        threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom) := by
  classical
  let G := ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L
  let k := fun σ : G => threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.toAlgHom)
  have hk : k 1 = 0 := by
    change threeAdicIdealOrder L (Ideal.span (Set.range fun x : ThreeAdicIntegers L =>
      x - x)) = 0
    simp only [sub_self, Set.range_const, Ideal.span_singleton_zero]
    change Multiset.count _ (UniqueFactorizationMonoid.normalizedFactors
      (0 : Ideal (ThreeAdicIntegers L))) = 0
    rw [UniqueFactorizationMonoid.normalizedFactors_zero, Multiset.count_zero]
  have hsum := Finset.sum_congr_set (ThreeAdicIntegralInertia L : Set G) k
    (fun σ => k σ.val) (fun _ _ => rfl)
    (fun σ hσ => threeAdicDisplacementIdealOrderZeroOutsideInertia L σ hσ)
  have hG := Finset.sum_erase_add Finset.univ k (Finset.mem_univ (1 : G))
  have hH := Finset.sum_erase_add Finset.univ
    (fun σ : ThreeAdicIntegralInertia L => k σ.val) (Finset.mem_univ 1)
  change _ + k 1 = _ at hH
  rw [hk, add_zero] at hG hH
  exact (threeAdicDifferentOrderEqSumAut L).trans (hG.trans (hsum.trans hH.symm))

/-- A relative Eisenstein generator has the same forbidden critical value
as the absolute different and largest inertia displacement. -/
theorem threeAdicRelativeMinpolyAddValNeCritical [IsGalois ℚ_[3] L] [Nontrivial C]
    (pc : PowerBasis ℤ_[3] C) (pb : PowerBasis C (ThreeAdicIntegers L))
    (hdim : pb.dim = threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}))
    (c : ℕ)
    (hbound : ∀ σ : ThreeAdicIntegralInertia L, σ ≠ 1 →
      threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom) ≤ c)
    (hmax : ∃ σ : ThreeAdicIntegralInertia L, σ ≠ 1 ∧
      threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom) = c)
    (hc : 0 < c) (x : ThreeAdicIntegers L) :
    IsDiscreteValuationRing.addVal (ThreeAdicIntegers L)
      (aeval x (minpoly C pb.gen)) ≠
        ((threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) + c - 1 : ℕ) :
          ℕ∞) := by
  classical
  rw [← eval_map_algebraMap, threeAdicRelativeMinpolyEqProdInertia L pc pb hdim,
    eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  exact AddValuation.orbitProdSubNeCritical (G := ThreeAdicIntegralInertia L)
    (IsDiscreteValuationRing.addVal (ThreeAdicIntegers L))
    (fun σ x => threeAdicAddValAut L σ.val x) pb.gen
    (fun σ => threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom))
    _ c (threeAdicAddValRelativeGenSubInertia L pc pb)
    (by
      convert (threeAdicDifferentOrderEqSumInertia L).symm using 2
      ext σ
      simp) hbound hmax hc x

end ThreeAdicPlan
