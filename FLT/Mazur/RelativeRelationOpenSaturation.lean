/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationOrbitOpens

/-!
# Saturating source opens under the full scheme relation

An open endpoint constructs the least invariant open containing a given open.
The construction preserves restriction to invariant domains, and its quotient
image is exactly the image of the original open. No affineness is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
universe u
namespace FLT.Mazur.RelativeRelationOrbit
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)

/-- The actual open image of a source open in the original orbit space. -/
def orbitImageOpen (W : U.left.Opens) : TopologicalSpace.Opens (Orbit e) :=
  ⟨projection e '' (W : Set U.left), projection_isOpenMap e hq _ W.isOpen⟩

/-- The least full-relation invariant open containing the supplied source open. -/
def saturateOpen (W : U.left.Opens) : InvariantOpens p q :=
  pullOpen e (orbitImageOpen e hq W)

/-- Saturation is the image under the second endpoint of the first endpoint's domain. -/
theorem saturateOpen_coe (W : U.left.Opens) :
    ((saturateOpen e hq W).val : Set U.left) = q.left '' (p.left ⁻¹' W) :=
  saturation_eq e W

/-- A point is in the saturation precisely when its orbit meets the supplied open. -/
theorem mem_saturateOpen_iff (W : U.left.Opens) (x : U.left) :
    x ∈ (saturateOpen e hq W).val ↔
      ∃ y ∈ W, projection e y = projection e x := Iff.rfl

/-- Every point of the original open belongs to its invariant saturation. -/
theorem le_saturateOpen (W : U.left.Opens) : W ≤ (saturateOpen e hq W).val :=
  fun x hx ↦ ⟨x, hx, rfl⟩

/-- Both original endpoints have exactly the same saturated domain. -/
theorem saturateOpen_preimage_eq (W : U.left.Opens) :
    p.left ⁻¹ᵁ (saturateOpen e hq W).val = q.left ⁻¹ᵁ (saturateOpen e hq W).val :=
  (saturateOpen e hq W).property

/-- Saturation is minimal among full-relation invariant containing opens. -/
theorem saturateOpen_le_iff (W : U.left.Opens) (B : InvariantOpens p q) :
    (saturateOpen e hq W).val ≤ B.val ↔ W ≤ B.val := by
  constructor
  · exact fun h ↦ (le_saturateOpen e hq W).trans h
  · intro h x hx
    obtain ⟨y, hy, he⟩ := (mem_saturateOpen_iff e hq W x).mp hx
    exact (invariant_mem_iff B ((projection_eq_iff e y x).mp he)).mp (h hy)

/-- Refining the original open refines its invariant saturation. -/
theorem saturateOpen_mono {W Z : U.left.Opens} (h : W ≤ Z) :
    (saturateOpen e hq W).val ≤ (saturateOpen e hq Z).val :=
  (saturateOpen_le_iff e hq W _).mpr (h.trans (le_saturateOpen e hq Z))

/-- An already invariant open is fixed by saturation. -/
theorem saturateOpen_of_invariant (B : InvariantOpens p q) :
    saturateOpen e hq B.val = B := by
  apply Subtype.ext
  exact le_antisymm ((saturateOpen_le_iff e hq B.val B).mpr le_rfl)
    (le_saturateOpen e hq B.val)

/-- Restricting to an invariant open commutes with full-relation saturation. -/
theorem saturateOpen_inf_invariant (W : U.left.Opens) (B : InvariantOpens p q) :
    (saturateOpen e hq (W ⊓ B.val)).val = (saturateOpen e hq W).val ⊓ B.val := by
  apply le_antisymm
  · exact le_inf (saturateOpen_mono e hq inf_le_left)
      ((saturateOpen_le_iff e hq _ B).mpr inf_le_right)
  · intro x hx
    obtain ⟨y, hy, he⟩ := (mem_saturateOpen_iff e hq W x).mp hx.1
    exact ⟨y, ⟨hy, (invariant_mem_iff B ((projection_eq_iff e y x).mp he)).mpr hx.2⟩, he⟩

/-- Descending the saturation adds no new points to the quotient image. -/
theorem descendOpen_saturateOpen (W : U.left.Opens) :
    descendOpen e (saturateOpen e hq W) = orbitImageOpen e hq W :=
  descendOpen_pullOpen e _

end FLT.Mazur.RelativeRelationOrbit
