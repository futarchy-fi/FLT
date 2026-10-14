/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Finite fibers on a specified Cartesian square

An injective target inclusion identifies the original point fiber with the
image of the corresponding changed fiber. This applies to the actual maps
of a closed or open base change without replacing the supplied schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CartesianFiniteFibers

variable {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {j : X' ⟶ X} {i : Y' ⟶ Y} (H : IsPullback f' j i f)

include H

/-- The source inclusion has exactly the inverse image of the target inclusion as its range. -/
theorem range_eq_preimage : Set.range j = f ⁻¹' Set.range i := by
  rw [← H.flip.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
  rw [Set.range_comp, Set.range_eq_univ.mpr
    (ConcreteCategory.bijective_of_isIso H.flip.isoPullback.hom.base).surjective,
    Set.image_univ, Scheme.Pullback.range_fst]

/-- The original point fiber is the image of the specified changed point fiber. -/
theorem image_fiber (hi : Function.Injective i) (y : Y') :
    j '' (f' ⁻¹' {y}) = f ⁻¹' {i y} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change f (j z) = i y
    change f' z = y at hz
    have hw := congrArg (fun a : X' ⟶ Y ↦ a z) H.w
    change i (f' z) = f (j z) at hw
    rw [← hw, hz]
  · intro hx
    have hx' : x ∈ Set.range j := by
      rw [range_eq_preimage H]
      exact ⟨y, hx.symm⟩
    obtain ⟨z, rfl⟩ := hx'
    refine ⟨z, ?_, rfl⟩
    apply hi
    have hw := congrArg (fun a : X' ⟶ Y ↦ a z) H.w
    exact hw.trans hx

/-- Finiteness of the actual changed fiber proves finiteness of the original fiber. -/
theorem finite_fiber (hi : Function.Injective i) (y : Y')
    (hy : (f' ⁻¹' {y}).Finite) : (f ⁻¹' {i y}).Finite := by
  rw [← image_fiber H hi y]
  exact hy.image j

omit H in
/-- An unchanged target neighborhood has singleton, hence finite, original point fibers. -/
theorem finite_fiber_of_restrict_isIso {X Y : Scheme} (g : X ⟶ Y) (U : Y.Opens)
    [IsIso (g ∣_ U)] (y : Y) (hy : y ∈ U) : (g ⁻¹' {y}).Finite := by
  have hfin : ((g ∣_ U) ⁻¹' {(⟨y, hy⟩ : U)}).Finite :=
    Set.Finite.preimage
      (ConcreteCategory.bijective_of_isIso (g ∣_ U).base).injective.injOn
      (Set.finite_singleton _)
  exact finite_fiber (isPullback_morphismRestrict g U) Subtype.val_injective ⟨y, hy⟩ hfin

end FLT.Mazur.CartesianFiniteFibers
