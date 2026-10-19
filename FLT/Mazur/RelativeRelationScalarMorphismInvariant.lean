/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationMinimalScalarEndpoints
public import FLT.Mazur.SchemeScalarAvoidanceCover

/-!
# Exact prescribed scalar characters along original relation arrows

The scalar morphism on the full prescribed open equalizes every original
arrow, as a scheme morphism. This retains residue maps and nilpotents and
requires neither completeness nor an affine source or a finite scalar map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val
local notation "s" => orbitScalarCoordinates e W
local notation "g₁" => (InvariantOpenRelationDiagram.fst p E).left
local notation "g₂" => (InvariantOpenRelationDiagram.snd p q E (pullOpen_preimage_eq e W)).left

/-- The full original restricted relation equalizes the unchanged scalar morphism. -/
theorem orbitScalarMorphism_equalizes : g₁ ≫ scalarMorphism s = g₂ ≫ scalarMorphism s := by
  rw [← scalarMorphism_comp, ← scalarMorphism_comp]
  congr 1
  ext r
  exact (orbitFunctions e W r).property

/-- Every original arrow preserves the full prescribed scalar character on arbitrary tests. -/
theorem orbitScalarMorphism_original_arrow {T : Scheme} (b c : T ⟶ (E).toScheme)
    (a : T ⟶ D.left) (ha : a ≫ p.left = b ≫ (E).ι)
    (hb : a ≫ q.left = c ≫ (E).ι) :
    b ≫ scalarMorphism s = c ≫ scalarMorphism s := by
  have hr : Set.range a ⊆ Set.range (p.left ⁻¹ᵁ E).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    change (a ≫ p.left) t ∈ E
    rw [ha]
    exact (b t).property
  let z := IsOpenImmersion.lift (p.left ⁻¹ᵁ E).ι a hr
  have hz : z ≫ (p.left ⁻¹ᵁ E).ι = a := IsOpenImmersion.lift_fac _ _ _
  have h₁ : z ≫ g₁ = b := by
    apply (cancel_mono (E).ι).mp
    change (z ≫ p.left.resLE E _ le_rfl) ≫ (E).ι = _
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hz]
    exact ha
  have h₂ : z ≫ g₂ = c := by
    apply (cancel_mono (E).ι).mp
    change (z ≫ q.left.resLE E _ (pullOpen_preimage_eq e W).le) ≫ (E).ι = _
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hz]
    exact hb
  rw [← h₁, ← h₂, Category.assoc, Category.assoc, orbitScalarMorphism_equalizes]

end FLT.Mazur.RelativeRelationOrbit
