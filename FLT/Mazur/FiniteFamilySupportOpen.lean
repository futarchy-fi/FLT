/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The support open of an actual finite scheme family

Remove the closed finite image of the complement of a chosen open in the
family. The resulting open is exactly the largest base open over which the
whole family lies in that open. No reducedness or nonempty-fiber assumption
is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {D S : Scheme.{u}} (p : D ⟶ S) [IsFinite p] (U : D.Opens)

/-- The actual open where every point of the finite family lies in the prescribed open. -/
def finiteFamilySupportOpen : S.Opens :=
  ⟨(p '' (U : Set D)ᶜ)ᶜ, (p.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩

/-- Membership means that the entire actual fiber lies in the prescribed open. -/
theorem mem_finiteFamilySupportOpen (s : S) :
    s ∈ finiteFamilySupportOpen p U ↔ ∀ x : D, p x = s → x ∈ U := by
  constructor
  · intro h x hx
    by_contra hU
    exact h ⟨x, hU, hx⟩
  · rintro h ⟨x, hx, hs⟩
    exact hx (h x hs)

/-- The whole family over its support open lies inside the prescribed open. -/
theorem finiteFamilySupportOpen_preimage_le : p ⁻¹ᵁ finiteFamilySupportOpen p U ≤ U := by
  intro x hx
  exact (mem_finiteFamilySupportOpen p U (p x)).mp hx x rfl

/-- The support open is the largest base open whose entire inverse image lies in the open. -/
theorem le_finiteFamilySupportOpen_iff (V : S.Opens) :
    V ≤ finiteFamilySupportOpen p U ↔ p ⁻¹ᵁ V ≤ U := by
  constructor
  · intro h x hx
    exact finiteFamilySupportOpen_preimage_le p U (h hx)
  · intro h s hs
    apply (mem_finiteFamilySupportOpen p U s).mpr
    intro x hx
    exact h (show p x ∈ V from hx ▸ hs)

/-- Enlarging the permitted family open enlarges the exact base support locus. -/
theorem finiteFamilySupportOpen_mono {V : D.Opens} (h : U ≤ V) :
    finiteFamilySupportOpen p U ≤ finiteFamilySupportOpen p V :=
  (le_finiteFamilySupportOpen_iff p V _).mpr ((finiteFamilySupportOpen_preimage_le p U).trans h)

end FLT.Mazur.FCurve
