/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ClosedSubsets

/-!
# Finite morphisms from proper integral curves

A nonconstant continuous closed map from a Noetherian T₀ irreducible space
of dimension at most one has finite fibers. Closed fibers are proper closed
subsets, while a fiber over a nonclosed point contains at most the generic point.

A proper scheme morphism with finite fibers is finite. This proves FC14 for
separated targets, without a smoothness or algebraic-closure assumption.
The dimension bound remains an explicit hypothesis.
-/

@[expose] public section

open Set TopologicalSpace

namespace FLT.Mazur.FCurve

/-- Nonconstant continuous closed maps from irreducible Noetherian curves have finite fibers. -/
theorem finite_fibers_of_isClosedMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NoetherianSpace X] [T0Space X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 1) {f : X → Y}
    (hf : Continuous f) (hclosed : IsClosedMap f) (hne : ∃ a b, f a ≠ f b)
    (y : Y) : (f ⁻¹' {y}).Finite := by
  by_cases hy : IsClosed ({y} : Set Y)
  · apply finite_of_isClosed_of_ne_univ hdim (hy.preimage hf)
    intro h
    obtain ⟨a, b, hab⟩ := hne
    have hall (x : X) : f x = y := by
      have hx : x ∈ f ⁻¹' {y} := h.symm ▸ Set.mem_univ x
      exact hx
    exact hab ((hall a).trans (hall b).symm)
  · have hgeneric (x : X) (hx : f x = y) : closure {x} = univ := by
      by_contra h
      obtain ⟨z, hz⟩ := eq_singleton_of_isClosed_of_isIrreducible hdim
        isClosed_closure isIrreducible_singleton.closure h
      have hxz : x = z := by
        have hxmem := subset_closure (mem_singleton x)
        rwa [hz, mem_singleton_iff] at hxmem
      have hc : IsClosed ({x} : Set X) := by
        simpa only [hz, ← hxz] using (isClosed_closure (s := ({x} : Set X)))
      exact hy (by simpa only [Set.image_singleton, hx] using hclosed {x} hc)
    apply Set.Subsingleton.finite
    intro a ha b hb
    exact (inseparable_iff_closure_eq.mpr
      ((hgeneric a ha).trans (hgeneric b hb).symm)).eq

open CategoryTheory AlgebraicGeometry

/-- A nonconstant morphism from a proper integral curve to a separated target is finite. -/
theorem nonconstantProperCurveFinite {K : Type*} [Field K]
    {X Y : Scheme} (x : X ⟶ Spec (CommRingCat.of K))
    (y : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) :
    NonconstantProperCurveFinite x y f := by
  intro hx hX hdim hy hcomp hne
  let : IsProper (f ≫ y) := hcomp.symm ▸ hx
  let : IsProper f := IsProper.of_comp f y
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace x
  let : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian x }
  let : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    (finite_fibers_of_isClosedMap hdim f.continuous f.isClosedMap hne)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end FLT.Mazur.FCurve
