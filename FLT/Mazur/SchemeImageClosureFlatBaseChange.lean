/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Image closures under flat base change

The full Cartesian pullback retains every point of a failed locus, including
its generizing centers. Flat locally finitely presented scalar changes commute
with its image closure. A single lifted scalar point therefore detects the
original obstruction; the scalar change need not be globally surjective.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeImageClosure
universe u
variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (K : Set X)

/-- The full pullback has exactly the inverse image of the original failed image. -/
theorem pullback_image :
    pullback.snd f g '' (pullback.fst f g ⁻¹' K) = g ⁻¹' (f '' K) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨pullback.fst f g z, hz, ?_⟩
    exact congrArg (fun h : pullback f g ⟶ S ↦ h z) (pullback.condition (f := f) (g := g))
  · rintro ⟨x, hx, he⟩
    obtain ⟨z, hz, hy⟩ := Scheme.Pullback.exists_preimage_pullback x y he
    exact ⟨z, by simpa only [Set.mem_preimage, hz] using hx, hy⟩

/-- Open scalar changes preserve all specialization limits of the full failed image. -/
theorem pullback_image_closure (hg : IsOpenMap g) :
    closure (pullback.snd f g '' (pullback.fst f g ⁻¹' K)) =
      g ⁻¹' closure (f '' K) := by
  rw [pullback_image, hg.preimage_closure_eq_closure_preimage g.continuous]

variable [Flat g] [LocallyOfFinitePresentation g]

/-- Flat locally finitely presented base change computes the unchanged obstruction closure. -/
theorem flat_pullback_image_closure :
    closure (pullback.snd f g '' (pullback.fst f g ⁻¹' K)) =
      g ⁻¹' closure (f '' K) :=
  pullback_image_closure f g K g.isOpenMap

/-- One lifted point outside the full branch obstruction excludes the original scalar point. -/
theorem not_mem_closure_of_flat_pullback (y : Y)
    (hy : y ∉ closure (pullback.snd f g '' (pullback.fst f g ⁻¹' K))) :
    g y ∉ closure (f '' K) := by
  rwa [flat_pullback_image_closure] at hy

/-- A branch neighborhood avoiding the failed image already excludes its closure at that point. -/
theorem not_mem_closure_of_flat_neighborhood (V : Y.Opens) (y : Y) (hy : y ∈ V)
    (hV : ∀ z : (pullback f g : Scheme), pullback.snd f g z ∈ V → pullback.fst f g z ∉ K) :
    g y ∉ closure (f '' K) := by
  apply not_mem_closure_of_flat_pullback f g K y
  intro hc
  obtain ⟨_, hv, z, hz, rfl⟩ := mem_closure_iff.mp hc V V.isOpen hy
  exact hV z hv hz

end FLT.Mazur.SchemeImageClosure
