/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.DedekindDomain.Completion.BaseChange
public import FLT.Mathlib.RingTheory.TraceDualBaseChange
public import FLT.Mathlib.RingTheory.TraceDualPi

/-!
# Trace-dual lattices and completed products

The tensor decomposition of completions identifies the completed global
trace-dual lattice with the product of the local trace-dual lattices.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Module Algebra

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace IsDedekindDomain.HeightOneSpectrum

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]
  [FiniteDimensional K L] [Module.Finite A B]
  (v : HeightOneSpectrum A)

open scoped TensorProduct.RightActions in
/-- The completed tensor decomposition, linear over the completed base field. -/
def completionProductEquiv :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      ∀ w : v.Extension B, w.1.adicCompletion L :=
  let e : v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      L ⊗[K] v.adicCompletion K :=
    { Algebra.TensorProduct.comm K (v.adicCompletion K) L with
      commutes' := fun _ ↦ rfl }
  e.trans
    (AlgEquiv.ofBijective (adicCompletion.baseChangeRight K L B v)
      (adicCompletion.baseChange_bijective K L B v))

/-- The completed tensor decomposition sends a pure tensor to the componentwise product. -/
theorem completionProductEquiv_tmul (x : v.adicCompletion K) (y : L)
    (w : v.Extension B) :
    completionProductEquiv A K L B v (x ⊗ₜ[K] y) w =
      algebraMap L (w.1.adicCompletion L) y *
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x := rfl

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct.RightActions in
omit [Module.Finite A B] in
/-- The completed integral lattice is the span of the diagonal global integers. -/
theorem span_range_algebraMap_eq_pi_integers :
    (Submodule.span (v.adicCompletionIntegers K)
      (Set.range (algebraMap B (∀ w : v.Extension B, w.1.adicCompletion L))) :
        Set (∀ w : v.Extension B, w.1.adicCompletion L)) =
      Set.univ.pi (fun w ↦ (w.1.adicCompletionIntegers L).carrier) := by
  let f := tensorAdicCompletionIntegersToPiRight K L B v
  have hft (b : B) (x : v.adicCompletionIntegers K) (w : v.Extension B) :
      f (b ⊗ₜ[A] x) w = algebraMap B (w.1.adicCompletion L) b *
        algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletion L) x := by
    change adicCompletion.baseChange K L B v
      (tensorAdicCompletionIntegersTo K L B v (b ⊗ₜ[A] x)) w = _
    rw [tensorAdicCompletionIntegersTo_tmul, adicCompletion.baseChange_tmul_apply,
      ← IsScalarTower.algebraMap_apply B L]
    rfl
  have hf : Submodule.span (v.adicCompletionIntegers K)
      (Set.range (algebraMap B (∀ w : v.Extension B, w.1.adicCompletion L))) =
        f.toLinearMap.range := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      refine ⟨b ⊗ₜ[A] 1, ?_⟩
      funext w
      simpa only [AlgHom.toLinearMap_apply, Pi.algebraMap_apply, map_one, mul_one]
        using hft b 1 w
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.inductionOn with
      | tmul b x =>
        have he : f (b ⊗ₜ[A] x) = x • algebraMap B
            (∀ w : v.Extension B, w.1.adicCompletion L) b := by
          funext w
          change f (b ⊗ₜ[A] x) w = algebraMap (v.adicCompletionIntegers K)
            (w.1.adicCompletion L) x * algebraMap B (w.1.adicCompletion L) b
          rw [hft, mul_comm]
        change f (b ⊗ₜ[A] x) ∈ _
        rw [he]
        exact Submodule.smul_mem _ x (Submodule.subset_span ⟨b, rfl⟩)
      | add x y hx hy =>
        simpa only [map_add] using Submodule.add_mem _ hx hy
  rw [hf]
  exact range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L B v

variable [Algebra.IsSeparable K L]

set_option backward.isDefEq.respectTransparency false in
/-- The trace dual of the completed global integer lattice is the completed
global trace dual. The basis hypothesis is satisfied by an integral basis
for an extension of number fields over the rationals. -/
theorem traceDual_span_completion
    {ι : Type*} [Finite ι] (b : Basis ι K L)
    (hb : (1 : Submodule B L).restrictScalars A = Submodule.span A (Set.range b)) :
    (traceForm (v.adicCompletion K) (∀ w : v.Extension B, w.1.adicCompletion L)).dualSubmodule
      (Submodule.span (v.adicCompletionIntegers K)
        (Set.range (algebraMap B (∀ w : v.Extension B, w.1.adicCompletion L)))) =
    Submodule.span (v.adicCompletionIntegers K)
      (algebraMap L (∀ w : v.Extension B, w.1.adicCompletion L) ''
        (Submodule.traceDual A K (1 : Submodule B L) : Set L)) := by
  let e := completionProductEquiv A K L B v
  let f := (e.toLinearEquiv.restrictScalars (v.adicCompletionIntegers K)).toLinearMap
  have he (x : L) : e (Algebra.TensorProduct.includeRight x) =
      algebraMap L (∀ w : v.Extension B, w.1.adicCompletion L) x := by
    funext w
    change completionProductEquiv A K L B v ((1 : v.adicCompletion K) ⊗ₜ[K] x) w = _
    rw [completionProductEquiv_tmul, map_one, mul_one]
    rfl
  have hm (T : Set L) :
      (Submodule.span (v.adicCompletionIntegers K)
        (Algebra.TensorProduct.includeRight '' T)).map f =
      Submodule.span (v.adicCompletionIntegers K)
        (algebraMap L (∀ w : v.Extension B, w.1.adicCompletion L) '' T) := by
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro x _
    exact he x
  have hN : algebraMap L (∀ w : v.Extension B, w.1.adicCompletion L) ''
      ((1 : Submodule B L) : Set L) =
      Set.range (algebraMap B (∀ w : v.Extension B, w.1.adicCompletion L)) := by
    rw [Submodule.one_eq_range]
    change _ '' Set.range (algebraMap B L) = _
    rw [← Set.range_comp]
    rfl
  have hd := b.dualSubmodule_span_image_baseChange
    (S := v.adicCompletionIntegers K) (F := v.adicCompletion K)
    ((1 : Submodule B L).restrictScalars A) hb
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  change (traceForm (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)).dualSubmodule
    (Submodule.span (v.adicCompletionIntegers K)
      (Algebra.TensorProduct.includeRight '' ((1 : Submodule B L) : Set L))) =
    Submodule.span (v.adicCompletionIntegers K)
      (Algebra.TensorProduct.includeRight ''
        (Submodule.traceDual A K (1 : Submodule B L) : Set L)) at hd
  rw [← hN, ← hm, e.mem_dualSubmodule_map_iff, hd, ← hm]
  constructor
  · intro hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
    have heq : z = x := e.injective hzx
    simpa only [heq] using hz

set_option backward.isDefEq.respectTransparency false in
/-- At each prime, the local trace-dual lattice is generated over the completed
base integers by the image of the global trace-dual lattice. -/
theorem traceDual_completion_eq_span
    {ι : Type*} [Finite ι] (b : Basis ι K L)
    (hb : (1 : Submodule B L).restrictScalars A = Submodule.span A (Set.range b))
    (w : v.Extension B) :
    letI : IsScalarTower (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
        (w.1.adicCompletion L) := .of_algebraMap_eq fun _ ↦ rfl
    (Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
      (1 : Submodule (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))).restrictScalars
        (v.adicCompletionIntegers K) =
    Submodule.span (v.adicCompletionIntegers K)
      (algebraMap L (w.1.adicCompletion L) ''
        (Submodule.traceDual A K (1 : Submodule B L) : Set L)) := by
  classical
  let _ (u : v.Extension B) : IsScalarTower (v.adicCompletionIntegers K)
      (u.1.adicCompletionIntegers L) (u.1.adicCompletion L) :=
    .of_algebraMap_eq fun _ ↦ rfl
  let := Extension.finite A K L B v
  let N (u : v.Extension B) : Submodule (v.adicCompletionIntegers K) (u.1.adicCompletion L) :=
    (1 : Submodule (u.1.adicCompletionIntegers L) (u.1.adicCompletion L)).restrictScalars _
  have hn (u : v.Extension B) : (N u : Set (u.1.adicCompletion L)) =
      (u.1.adicCompletionIntegers L).carrier := by
    ext x
    change x ∈ (1 : Submodule (u.1.adicCompletionIntegers L) (u.1.adicCompletion L)) ↔ _
    rw [Submodule.mem_one]
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have hp : Submodule.span (v.adicCompletionIntegers K)
      (Set.range (algebraMap B (∀ u : v.Extension B, u.1.adicCompletion L))) =
      Submodule.pi Set.univ N := by
    apply SetLike.coe_injective
    rw [span_range_algebraMap_eq_pi_integers A K L B v, Submodule.coe_pi]
    congr 1
    funext u
    exact (hn u).symm
  have h := traceDual_span_completion A K L B v b hb
  rw [hp, Algebra.dualSubmodule_pi] at h
  have hm := congrArg (Submodule.map (LinearMap.proj w)) h
  rw [Submodule.map_span, Set.image_image] at hm
  have hi : (Submodule.pi Set.univ
      (fun u ↦ (traceForm (v.adicCompletion K) (u.1.adicCompletion L)).dualSubmodule (N u))).map
      (LinearMap.proj w) =
      (traceForm (v.adicCompletion K) (w.1.adicCompletion L)).dualSubmodule (N w) := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy w (Set.mem_univ w)
    · intro x hx
      refine Submodule.mem_map.mpr ⟨Pi.single w x, ?_, by simp⟩
      exact Submodule.le_comap_single_pi _ hx
  rw [hi] at hm
  exact hm

end IsDedekindDomain.HeightOneSpectrum
