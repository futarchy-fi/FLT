/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Finite principal covers inside an actual scheme image

A compact open in an affine scheme has a finite cover by its own actual
global functions. If the open lies in a morphism's image, restriction above
every selected principal open is surjective on points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.FinitePrincipalImageCover
variable {X Y : Scheme.{u}}

/-- Finite actual global coefficients cover a compact open without leaving it. -/
theorem exists_coefficients [IsAffine Y] (U : Y.Opens) (hc : IsCompact (U : Set Y)) :
    ∃ s : Finset Γ(Y, ⊤), (∀ r ∈ s, Y.basicOpen r ≤ U) ∧
      (⨆ r : s, Y.basicOpen r.val) = U := by
  classical
  let I := {r : Γ(Y, ⊤) // Y.basicOpen r ≤ U}
  have hcover : (U : Set Y) ⊆ ⋃ r : I, (Y.basicOpen r.val : Set Y) := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := (isAffineOpen_top Y).exists_basicOpen_le ⟨x, hx⟩ (by trivial)
    exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hxr⟩
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun r : I ↦ (Y.basicOpen r.val : Set Y))
    (fun r ↦ (Y.basicOpen r.val).isOpen) hcover
  refine ⟨t.image Subtype.val, ?_, le_antisymm ?_ ?_⟩
  · intro r hr
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hr
    exact s.property
  · apply iSup_le
    intro r
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp r.property
    exact hs ▸ s.property
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨⟨r.val, Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩, hxr⟩

/-- Restricting above any actual-image open gives a surjective morphism. -/
theorem restriction_surjective (g : X ⟶ Y) (U : Y.Opens)
    (hU : (U : Set Y) ⊆ Set.range g) : Surjective (g ∣_ U) := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := hU y.property
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change g x ∈ U
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact (morphismRestrict_base_coe g U _).trans hx

/-- Every coefficient in the finite open cover gives an actual surjective principal model. -/
theorem exists_surjective_principal_cover [IsAffine Y] (g : X ⟶ Y) (U : Y.Opens)
    (hc : IsCompact (U : Set Y)) (hU : (U : Set Y) ⊆ Set.range g) :
    ∃ s : Finset Γ(Y, ⊤), (⨆ r : s, Y.basicOpen r.val) = U ∧
      ∀ r ∈ s, Y.basicOpen r ≤ U ∧ Surjective (g ∣_ Y.basicOpen r) := by
  obtain ⟨s, hs, he⟩ := exists_coefficients U hc
  exact ⟨s, he, fun r hr ↦ ⟨hs r hr,
    restriction_surjective g _ (fun _ hx ↦ hU (hs r hr hx))⟩⟩

end FLT.Mazur.FinitePrincipalImageCover
