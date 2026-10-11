/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationOrbitTopology

/-!
# Opens of the orbit space and invariant source opens

The quotient opens are exactly the opens whose two inverse images on the
actual relation agree. This supplies the domains for invariant regular
functions without assuming that the orbit space is already a scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
universe u
namespace FLT.Mazur.RelativeRelationOrbit
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- Source opens on which the two relation projections agree setwise. -/
def InvariantOpens (p q : A ⟶ U) :=
  {V : U.left.Opens // p.left ⁻¹ᵁ V = q.left ⁻¹ᵁ V}

instance invariantOpensPartialOrder : PartialOrder (InvariantOpens p q) :=
  inferInstanceAs (PartialOrder {V : U.left.Opens // p.left ⁻¹ᵁ V = q.left ⁻¹ᵁ V})

/-- An invariant open is a union of whole actual orbits. -/
theorem invariant_mem_iff (V : InvariantOpens p q) {x y : U.left}
    (h : Related p q x y) : x ∈ V.val ↔ y ∈ V.val := by
  obtain ⟨a, rfl, rfl⟩ := h
  exact Set.ext_iff.mp (congrArg SetLike.coe V.property) a

/-- Saturating an invariant open leaves it unchanged. -/
theorem invariant_saturation (V : InvariantOpens p q) :
    projection e ⁻¹' (projection e '' (V.val : Set U.left)) = V.val := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    exact (invariant_mem_iff V ((projection_eq_iff e y x).mp he)).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Pullback of a quotient open is an invariant source open. -/
def pullOpen (W : TopologicalSpace.Opens (Orbit e)) : InvariantOpens p q :=
  ⟨⟨projection e ⁻¹' W, W.isOpen.preimage (projection_continuous e)⟩, by
    ext a
    change projection e (p.left a) ∈ W ↔ projection e (q.left a) ∈ W
    rw [projection_pair]⟩

/-- The image of an invariant source open is an actual quotient open. -/
def descendOpen (V : InvariantOpens p q) : TopologicalSpace.Opens (Orbit e) :=
  ⟨projection e '' (V.val : Set U.left), (projection_isQuotientMap e).isOpen_preimage.mp
    (by rw [invariant_saturation]; exact V.val.isOpen)⟩

/-- Pulling back a descended open recovers precisely the supplied source open. -/
theorem pullOpen_descendOpen (V : InvariantOpens p q) :
    pullOpen e (descendOpen e V) = V :=
  Subtype.ext (TopologicalSpace.Opens.ext (invariant_saturation e V))

/-- Every quotient open is recovered from its source inverse image. -/
theorem descendOpen_pullOpen (W : TopologicalSpace.Opens (Orbit e)) :
    descendOpen e (pullOpen e W) = W :=
  TopologicalSpace.Opens.ext (Set.image_preimage_eq _ (projection_surjective e))

/-- Quotient opens are exactly invariant source opens, with the same inclusion order. -/
def opensOrderIso : TopologicalSpace.Opens (Orbit e) ≃o InvariantOpens p q where
  toFun := pullOpen e
  invFun := descendOpen e
  left_inv := descendOpen_pullOpen e
  right_inv := pullOpen_descendOpen e
  map_rel_iff' := by
    intro W Z
    change projection e ⁻¹' (W : Set (Orbit e)) ⊆ projection e ⁻¹' Z ↔ W ≤ Z
    exact (projection_surjective e).preimage_subset_preimage_iff

/-- The invariant domain used for both pullbacks of regular functions on a quotient open. -/
theorem pullOpen_preimage_eq (W : TopologicalSpace.Opens (Orbit e)) :
    p.left ⁻¹ᵁ (pullOpen e W).val = q.left ⁻¹ᵁ (pullOpen e W).val :=
  (pullOpen e W).property

end FLT.Mazur.RelativeRelationOrbit
