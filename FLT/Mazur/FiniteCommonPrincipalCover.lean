/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Finite common principal covers of affine intersections

Compactness of an affine intersection selects finitely many opens which are
principal in both ambient charts. The two actual functions and their equal
open subscheme are retained, rather than just an abstract affine cover.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {X : Scheme.{u}} {U V : X.Opens}

/-- A compact intersection has a finite cover principal in each of its two charts. -/
theorem exists_finite_common_principal_cover (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hc : IsCompact (U ⊓ V : Set X)) :
    ∃ s : Finset (Γ(X, U) × Γ(X, V)),
      (∀ p ∈ s, X.basicOpen p.1 = X.basicOpen p.2) ∧
      (⨆ p : s, X.basicOpen p.val.1) = U ⊓ V := by
  classical
  let T := {p : Γ(X, U) × Γ(X, V) // X.basicOpen p.1 = X.basicOpen p.2}
  have hcover : (U ⊓ V : Set X) ⊆ ⋃ p : T, (X.basicOpen p.val.1 : Set X) := by
    intro x hx
    obtain ⟨f, g, hfg, hx⟩ := exists_basicOpen_le_affine_inter hU hV x hx
    exact Set.mem_iUnion.mpr ⟨⟨(f, g), hfg⟩, hx⟩
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover
    (fun p : T ↦ (X.basicOpen p.val.1 : Set X)) (fun _ ↦ (X.basicOpen _).isOpen) hcover
  refine ⟨t.image Subtype.val, ?_, le_antisymm ?_ ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  · apply iSup_le
    intro p
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp p.property
    have he : X.basicOpen p.val.1 = X.basicOpen p.val.2 := hq ▸ q.property
    exact le_inf (X.basicOpen_le _) (he ▸ X.basicOpen_le p.val.2)
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨p.val, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩, hxp⟩

/-- Quasi-separatedness supplies compactness without a finite-presentation hypothesis. -/
theorem exists_finite_common_principal_cover_of_quasiSeparated [QuasiSeparatedSpace X]
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ∃ s : Finset (Γ(X, U) × Γ(X, V)),
      (∀ p ∈ s, X.basicOpen p.1 = X.basicOpen p.2) ∧
      (⨆ p : s, X.basicOpen p.val.1) = U ⊓ V :=
  exists_finite_common_principal_cover hU hV
    (quasiSeparatedSpace_iff_forall_affineOpens.mp inferInstance ⟨U, hU⟩ ⟨V, hV⟩)

end FLT.Mazur.Approximation
