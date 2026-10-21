/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFlatScalarVanishingNeighborhood

/-!
# One original solution open for a whole flat branch neighborhood

The open is the inverse image of the open scalar branch image. It is chosen
before any section. Every section vanishing on the full branch pullback
vanishes on this same original open, so uniform multipliers can be chosen
before any boundary numerator or family of boundary values.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
open SchemeAdicVanishingNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X Y : Scheme} (s : R →+* Γ(X, ⊤))
  (g : Y ⟶ Spec (.of R)) [Flat g] [LocallyOfFinitePresentation g] (V : Y.Opens)
local notation "π" => scalarMorphism s
local notation "k" => pullback.fst π g
local notation "h" => pullback.snd π g

/-- The original full inverse image of the open scalar branch image. -/
def scalarBranchSolutionOpen : X.Opens :=
  π ⁻¹ᵁ ⟨g '' (V : Set Y), g.isOpenMap _ V.isOpen⟩

/-- Every original arrow over any point of the branch image lies in the common open. -/
theorem mem_scalarBranchSolutionOpen (x : X) :
    x ∈ scalarBranchSolutionOpen s g V ↔ ∃ y ∈ V, g y = π x := Iff.rfl

/-- Full branch equations descend to the common original open, independent of the section. -/
theorem scalarBranchSolutionOpen_le_vanishing (a : Γ(X, ⊤))
    (hV : (pullback π g : Scheme).presheaf.map
      (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op ((k).appTop a) = 0) :
    scalarBranchSolutionOpen s g V ≤ vanishingOpen a := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (mem_scalarBranchSolutionOpen s g V x).mp hx
  obtain ⟨z, hzx, hzy⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy.symm
  have hz : z ∈ h ⁻¹ᵁ V := by change h z ∈ V; rwa [hzy]
  have he := (flat_germ_appTop_eq_zero_iff k a z).mp
    (le_vanishingOpen _ (h ⁻¹ᵁ V) hV hz)
  change k z ∈ vanishingOpen a at he
  rwa [hzx] at he

/-- The full original equation holds on the constructed common open itself. -/
theorem scalarBranchSolutionOpen_restrict_zero (a : Γ(X, ⊤))
    (hV : (pullback π g : Scheme).presheaf.map
      (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op ((k).appTop a) = 0) :
    (scalarBranchSolutionOpen s g V).ι.appTop a = 0 := by
  let i := homOfLE (scalarBranchSolutionOpen_le_vanishing s g V a hV)
  have he : (scalarBranchSolutionOpen s g V).ι =
      X.homOfLE i.le ≫ (vanishingOpen a).ι := by simp
  rw [he, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply,
    vanishingOpen_inclusion_zero, map_zero]

/-- Every point of the branch neighborhood has an original denominator for the common open. -/
theorem exists_scalar_for_branchSolutionOpen (y : Y) (hy : y ∈ V) :
    ∃ r : R, r ∉ (g y).asIdeal ∧ X.basicOpen (s r) ≤ scalarBranchSolutionOpen s g V := by
  obtain ⟨_, ⟨r, rfl⟩, hry, hr⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
      (g.isOpenMap _ V.isOpen) (g y) ⟨y, hy, rfl⟩
  refine ⟨r, hry, ?_⟩
  intro x hx
  apply hr
  change x ∈ π ⁻¹ᵁ PrimeSpectrum.basicOpen r
  rwa [scalarMorphism_preimage]

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
