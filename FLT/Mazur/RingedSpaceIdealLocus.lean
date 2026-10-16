/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Topology.NoetherianSpace

/-!
# Open loci defined by ideals of sections

The union of unit loci of an ideal is unchanged by taking its radical.
On a Noetherian space finitely many actual elements of that ideal suffice,
without requiring its section ring to be Noetherian.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur
universe u
variable (X : RingedSpace.{u}) (W : Opens X)

/-- The open where at least one member of the section ideal is a unit. -/
def sectionIdealOpen (I : Ideal (X.presheaf.obj (op W))) : Opens X :=
  ⨆ s : I, X.basicOpen s.val

/-- A point belongs precisely when an actual ideal element is invertible there. -/
theorem mem_sectionIdealOpen (I : Ideal (X.presheaf.obj (op W))) (x : X) :
    x ∈ sectionIdealOpen X W I ↔ ∃ s ∈ I, x ∈ X.basicOpen s := by
  simp only [sectionIdealOpen, Opens.mem_iSup, Subtype.exists, exists_prop]

/-- The constructed open remains inside the section domain. -/
theorem sectionIdealOpen_le (I : Ideal (X.presheaf.obj (op W))) :
    sectionIdealOpen X W I ≤ W :=
  iSup_le fun _ ↦ X.basicOpen_le _

/-- Enlarging an ideal enlarges its unit locus. -/
theorem sectionIdealOpen_mono {I J : Ideal (X.presheaf.obj (op W))} (h : I ≤ J) :
    sectionIdealOpen X W I ≤ sectionIdealOpen X W J := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_sectionIdealOpen X W I x).mp hx
  exact (mem_sectionIdealOpen X W J x).mpr ⟨s, h hs, hx⟩

/-- Finite powers introduce no extra points into the ideal unit locus. -/
theorem sectionIdealOpen_radical (I : Ideal (X.presheaf.obj (op W))) :
    sectionIdealOpen X W I.radical = sectionIdealOpen X W I := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hx⟩ := (mem_sectionIdealOpen X W I.radical x).mp hx
    obtain ⟨n, hn⟩ := hs
    have hxW := X.basicOpen_le s hx
    refine (mem_sectionIdealOpen X W I x).mpr ⟨s ^ n, hn, ?_⟩
    rw [X.mem_basicOpen _ x hxW, map_pow]
    exact ((X.mem_basicOpen s x hxW).mp hx).pow n
  · exact sectionIdealOpen_mono X W Ideal.le_radical

/-- The unit ideal covers the whole domain. -/
theorem sectionIdealOpen_top : sectionIdealOpen X W ⊤ = W := by
  apply le_antisymm (sectionIdealOpen_le X W ⊤)
  intro x hx
  apply (mem_sectionIdealOpen X W ⊤ x).mpr
  exact ⟨1, trivial, by simpa only [X.basicOpen_of_isUnit isUnit_one] using hx⟩

/-- Noetherian topology gives finitely many actual denominators covering this locus. -/
theorem sectionIdealOpen_finite_cover [NoetherianSpace X]
    (I : Ideal (X.presheaf.obj (op W))) :
    ∃ s : Finset I, (sectionIdealOpen X W I : Set X) =
      ⋃ a ∈ s, (X.basicOpen a.val : Set X) := by
  have hc := NoetherianSpace.isCompact (sectionIdealOpen X W I : Set X)
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover (fun a : I ↦ (X.basicOpen a.val : Set X))
      (fun a ↦ (X.basicOpen a.val).isOpen) (by
        intro x hx
        obtain ⟨a, ha, hx⟩ := (mem_sectionIdealOpen X W I x).mp hx
        exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hx⟩)
  refine ⟨s, Set.Subset.antisymm hs ?_⟩
  intro x hx
  obtain ⟨a, _, hx⟩ := Set.mem_iUnion₂.mp hx
  exact (mem_sectionIdealOpen X W I x).mpr ⟨a.val, a.property, hx⟩

end FLT.Mazur
