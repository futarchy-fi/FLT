/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedActionComplete
public import FLT.Mazur.FiniteGroupEnvelopeNeighborhood

/-!
# Finite normalized orbits and their stable affine neighborhoods

The endpoint-moving action gives actual finite stable sets of scheme points.
An affine envelope supplies stable affine neighborhoods inside any prescribed
open containing the orbit. This alone makes no claim about extra original arrows.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
local notation "N" => source p q I o

/-- The actual finite orbit in the normalized source, with its moving original endpoints. -/
def frameOrbit (x : N) : Set N := Set.range (fun σ : Equiv.Perm I ↦ (action e I o σ).hom x)

/-- The whole normalized orbit is finite. -/
theorem frameOrbit_finite (x : N) : (frameOrbit e I o x).Finite := Set.finite_range _

/-- The initial source point belongs to its normalized orbit. -/
theorem mem_frameOrbit (x : N) : x ∈ frameOrbit e I o x := by
  refine ⟨1, ?_⟩
  change (action e I o 1).hom x = x
  rw [map_one]
  rfl

/-- Every actual normalized permutation preserves the entire finite orbit. -/
theorem frameOrbit_stable (x : N) (τ : Equiv.Perm I) :
    (action e I o τ).hom '' frameOrbit e I o x ⊆ frameOrbit e I o x := by
  rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
  exact ⟨τ * σ, (FiniteGroupNeighborhood.action_mul_apply (action e I o) τ σ x).symm⟩

/-- A complete geometric frame supplies complete representatives of its whole finite orbit. -/
theorem frameOrbit_complete_representative {K : Type} [Field K]
    (u : Spec (.of K) ⟶ N) (hu : Complete I o u) (x : N)
    (hx : x ∈ frameOrbit e I o (u default)) :
    ∃ v : Spec (.of K) ⟶ N, v default = x ∧ Complete I o v := by
  obtain ⟨σ, hσ⟩ := hx
  exact ⟨u ≫ (action e I o σ).hom, hσ, action_complete e I o u σ hu⟩

/-- Every open containing a normalized orbit admits an actual stable affine subneighborhood. -/
theorem exists_frameOrbit_affine_neighborhood {Y : Scheme} [IsAffine Y]
    (j : N ⟶ Y) [IsOpenImmersion j] (x : N) (W : (source p q I o).Opens)
    (hx : frameOrbit e I o x ⊆ W) :
    ∃ U : (source p q I o).Opens, IsAffineOpen U ∧ frameOrbit e I o x ⊆ U ∧ U ≤ W ∧
      ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ U = U :=
  FiniteGroupNeighborhood.exists_stable_affine_neighborhood (action e I o) j
    (frameOrbit e I o x) (frameOrbit_finite e I o x) (frameOrbit_stable e I o x) W hx

end FLT.Mazur.EquivalenceRelationNormalizedFrames
