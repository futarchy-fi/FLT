/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitTopology

/-!
# Opens of the orbit space and invariant source opens

The quotient opens are exactly the opens whose two inverse images on the
actual relation agree. This supplies the domains for invariant regular
functions without assuming that the orbit space is already a scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- Source opens on which the two relation projections agree setwise. -/
def InvariantOpens :=
  {V : (U).Opens // src ⁻¹ᵁ V = tgt ⁻¹ᵁ V}

instance invariantOpensPartialOrder : PartialOrder (InvariantOpens n) :=
  inferInstanceAs (PartialOrder {V : (U).Opens // src ⁻¹ᵁ V = tgt ⁻¹ᵁ V})

/-- An invariant open is a union of whole actual orbits. -/
theorem invariant_mem_iff (V : InvariantOpens n) {x y : U}
    (h : Related n x y) : x ∈ V.val ↔ y ∈ V.val := by
  obtain ⟨a, rfl, rfl⟩ := h
  exact Set.ext_iff.mp (congrArg SetLike.coe V.property) a

/-- Saturating an invariant open leaves it unchanged. -/
theorem invariant_saturation (V : InvariantOpens n) :
    projection n ⁻¹' (projection n '' (V.val : Set U)) = V.val := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    exact (invariant_mem_iff n V ((projection_eq_iff n y x).mp he)).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Pullback of a quotient open is an invariant source open. -/
def pullOpen (W : TopologicalSpace.Opens (Orbit n)) : InvariantOpens n :=
  ⟨⟨projection n ⁻¹' W, W.isOpen.preimage (projection_continuous n)⟩, by
    ext a
    change projection n (src a) ∈ W ↔ projection n (tgt a) ∈ W
    rw [projection_pair]⟩

/-- The image of an invariant source open is an actual quotient open. -/
def descendOpen (V : InvariantOpens n) : TopologicalSpace.Opens (Orbit n) :=
  ⟨projection n '' (V.val : Set U), (projection_isQuotientMap n).isOpen_preimage.mp
    (by rw [invariant_saturation]; exact V.val.isOpen)⟩

/-- Pulling back a descended open recovers precisely the supplied source open. -/
theorem pullOpen_descendOpen (V : InvariantOpens n) :
    pullOpen n (descendOpen n V) = V :=
  Subtype.ext (TopologicalSpace.Opens.ext (invariant_saturation n V))

/-- Every quotient open is recovered from its source inverse image. -/
theorem descendOpen_pullOpen (W : TopologicalSpace.Opens (Orbit n)) :
    descendOpen n (pullOpen n W) = W :=
  TopologicalSpace.Opens.ext (Set.image_preimage_eq _ (projection_surjective n))

/-- Quotient opens are exactly invariant source opens, with the same inclusion order. -/
def opensOrderIso : TopologicalSpace.Opens (Orbit n) ≃o InvariantOpens n where
  toFun := pullOpen n
  invFun := descendOpen n
  left_inv := descendOpen_pullOpen n
  right_inv := pullOpen_descendOpen n
  map_rel_iff' := by
    intro W Z
    change projection n ⁻¹' (W : Set (Orbit n)) ⊆ projection n ⁻¹' Z ↔ W ≤ Z
    exact (projection_surjective n).preimage_subset_preimage_iff

/-- The invariant domain used for both pullbacks of regular functions on a quotient open. -/
theorem pullOpen_preimage_eq (W : TopologicalSpace.Opens (Orbit n)) :
    src ⁻¹ᵁ (pullOpen n W).val = tgt ⁻¹ᵁ (pullOpen n W).val :=
  (pullOpen n W).property

end FLT.Mazur.CyclicCharacteristicOrbit
