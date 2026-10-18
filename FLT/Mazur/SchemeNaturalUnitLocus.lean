/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The actual open locus where a natural degree is invertible

The principal open of a natural number is preserved by every scheme morphism.
Intersecting with it preserves stable charts and affine charts, and produces
an actual unit in their coordinate rings. No coverage assertion is made for
points where the degree is not a unit in the original stalk.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.SchemeNaturalUnitLocus
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (X : Scheme.{0}) (n : ℕ)

/-- The principal open of the degree as an actual global section. -/
def locus : X.Opens := X.basicOpen (n : Γ(X, ⊤))

/-- Every scheme morphism pulls back the degree locus exactly. -/
theorem preimage {Y : Scheme.{0}} (f : X ⟶ Y) : f ⁻¹ᵁ locus Y n = locus X n := by
  rw [locus, Scheme.preimage_basicOpen_top, map_natCast]
  rfl

/-- The degree becomes a unit on its entire principal open, including nilpotents. -/
theorem isUnit : IsUnit (n : Γ((locus X n).toScheme, ⊤)) := by
  have hh := X.toRingedSpace.isUnit_res_basicOpen (n : Γ(X, ⊤))
  have hm := hh.map (locus X n).topIso.inv.hom
  simpa only [map_natCast] using hm

/-- Every smaller actual open chart inherits the unit degree. -/
theorem isUnit_on (U : X.Opens) (hU : U ≤ locus X n) :
    IsUnit (n : Γ(U.toScheme, ⊤)) := by
  simpa only [map_natCast] using
    (isUnit X n).map (X.homOfLE hU).appTop.hom

/-- Membership tests the degree in the original stalk, without reduction. -/
theorem mem_iff (x : X) : x ∈ locus X n ↔ IsUnit (n : X.presheaf.stalk x) := by
  rw [locus, Scheme.mem_basicOpen X _ x (by trivial), map_natCast]

/-- Intersection with the degree locus is the principal open in a given chart. -/
theorem inter_eq (U : X.Opens) : U ⊓ locus X n = X.basicOpen (n : Γ(X, U)) := by
  have hh := X.basicOpen_res (n : Γ(X, ⊤)) (homOfLE (show U ≤ ⊤ from le_top)).op
  simpa only [map_natCast, locus] using hh.symm

/-- Shrinking an affine chart to the unit-degree locus preserves affineness. -/
theorem isAffineOpen_inter (U : X.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (U ⊓ locus X n) := by
  rw [inter_eq]
  exact hU.basicOpen _

/-- Every automorphism preserves the degree locus, so stable intersections stay stable. -/
theorem stable_inter {G : Type} [Group G] (ρ : G →* Aut X)
    (U : X.Opens) (hU : ∀ g, (ρ g).hom ⁻¹ᵁ U = U) (g : G) :
    (ρ g).hom ⁻¹ᵁ (U ⊓ locus X n) = U ⊓ locus X n := by
  rw [Scheme.Hom.preimage_inf, hU, preimage]

/-- A point with unit degree remains in the refined affine chart. -/
theorem mem_inter (U : X.Opens) (x : X) (hx : x ∈ U)
    (hn : IsUnit (n : X.presheaf.stalk x)) : x ∈ U ⊓ locus X n :=
  ⟨hx, (mem_iff X n x).mpr hn⟩

end FLT.Mazur.SchemeNaturalUnitLocus
