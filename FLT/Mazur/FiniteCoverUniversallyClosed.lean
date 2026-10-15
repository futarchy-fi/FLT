/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Universal closedness detected by a finite joint source cover

Actual finite families of source maps suffice; no single global section or
chosen residue branch is needed. Cartesian lifting retains joint coverage
under every base change, so closedness of the composites descends universally.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteCoverUniversallyClosed
universe u v
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {I : Type v} [Finite I] (E : I → Scheme.{u}) (g : ∀ i, E i ⟶ X)
  (hg : ∀ x : X, ∃ i, ∃ z : E i, g i z = x)

include hg

/-- Finite joint coverage descends closedness from the actual composites. -/
theorem isClosedMap (hc : ∀ i, IsClosedMap (g i ≫ f)) : IsClosedMap f := by
  intro Z hZ
  have he : f '' Z = ⋃ i, (g i ≫ f) '' (g i ⁻¹' Z) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, z, rfl⟩ := hg x
      exact Set.mem_iUnion.mpr ⟨i, z, hx, rfl⟩
    · intro hy
      obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
      exact ⟨g i z, hz, rfl⟩
  rw [he]
  exact isClosed_iUnion_of_finite fun i ↦ hc i _ (hZ.preimage (g i).continuous)

/-- Universal closedness descends from any finite jointly covering family of composites. -/
theorem universallyClosed [∀ i, UniversallyClosed (g i ≫ f)] : UniversallyClosed f := by
  constructor
  intro X' Y' a b f' H
  let E' (i : I) := pullback a (g i)
  let g' (i : I) : E' i ⟶ X' := pullback.fst a (g i)
  apply isClosedMap f' E' g'
  · intro x
    obtain ⟨i, z, hz⟩ := hg (a x)
    obtain ⟨e, he, _⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback a (g i)) x z hz.symm
    exact ⟨i, e, he⟩
  · intro i
    exact UniversallyClosed.universally_isClosedMap _ _ _
      ((IsPullback.of_hasPullback a (g i)).paste_horiz H)

end FLT.Mazur.FiniteCoverUniversallyClosed
