/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeTupleOpenEmbedding
public import FLT.Mazur.RelativeDistinctTuples
public import FLT.Mazur.FiniteGroupEnvelopeNeighborhood

/-!
# Affine envelopes and stable neighborhoods of ordered distinct points

Embed the entire ordered-point scheme into the affine tuple scheme of an
original affine envelope. Finite permutation orbits therefore have stable
affine neighborhoods without assuming finiteness of the original source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} [IsAffine S] {E F : Over S} [IsSeparated E.hom]
  (j : E ⟶ F) [IsOpenImmersion j.left] [IsAffine F.left] (n : ℕ)

/-- The entire distinct-tuple scheme embeds in the affine tuple envelope. -/
def distinctEnvelopeMap : (distinctScheme E (Fin n)).left ⟶ (tuples F (Fin n)).left :=
  (distinctInclusion E (Fin n)).left ≫ (tupleMap j (Fin n)).left

instance distinctEnvelopeMap_open : IsOpenImmersion (distinctEnvelopeMap j n) := by
  let _ := finTupleMap_open j n
  change IsOpenImmersion ((distinctOpen E (Fin n)).ι ≫ (tupleMap j (Fin n)).left)
  infer_instance

include j in
/-- Every finite permutation-stable set admits a stable affine neighborhood. -/
theorem exists_distinct_stable_affine (s : Set (distinctScheme E (Fin n)).left)
    (hs : s.Finite) (hi : ∀ e : Equiv.Perm (Fin n), (distinctAction E (Fin n) e).hom '' s ⊆ s)
    (W : (distinctScheme E (Fin n)).left.Opens) (hsW : s ⊆ W) :
    ∃ U : (distinctScheme E (Fin n)).left.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W ∧
      ∀ e : Equiv.Perm (Fin n), (distinctAction E (Fin n) e).hom ⁻¹ᵁ U = U := by
  let _ := finTuples_affine F n
  exact FiniteGroupNeighborhood.exists_stable_affine_neighborhood
    (distinctAction E (Fin n)) (distinctEnvelopeMap j n) s hs hi W hsW

include j in
/-- In particular every original frame has a permutation-stable affine neighborhood. -/
theorem exists_distinct_orbit_affine (x : (distinctScheme E (Fin n)).left) :
    ∃ U : (distinctScheme E (Fin n)).left.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ e : Equiv.Perm (Fin n), (distinctAction E (Fin n) e).hom ⁻¹ᵁ U = U := by
  let ρ := distinctAction E (Fin n)
  let s := Set.range fun e : Equiv.Perm (Fin n) ↦ (ρ e).hom x
  have hi (g : Equiv.Perm (Fin n)) : (ρ g).hom '' s ⊆ s := by
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨g * h, (FiniteGroupNeighborhood.action_mul_apply ρ g h x).symm⟩
  obtain ⟨U, hU, hsU, _, he⟩ := exists_distinct_stable_affine j n s
    (Set.finite_range _) hi ⊤ (by intro y hy; trivial)
  refine ⟨U, hU, hsU ?_, he⟩
  refine ⟨1, ?_⟩
  change (ρ 1).hom x = x
  rw [map_one]
  rfl

end FLT.Mazur.RelativeOrderedTuples
