/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFullFiberRestriction

/-!
# Full-envelope interiors under actual source inclusions

A full independent envelope on an open source gives a full original envelope
at its image. The product pullback retains every independent residue branch.
For an invariant open inclusion the interiors agree exactly by restriction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left] {B : Over (Spec (.of R))}
  (v : B ⟶ A) [IsOpenImmersion v.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "j'" => Over.Hom.left (toEnvelope f hL d V c (v ≫ k))
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "π'" => Over.Hom.left (prod.fst : prod B V ⟶ B)
local notation "U" => fullEnvelopeInterior f hL d V c k
local notation "U'" => fullEnvelopeInterior f hL d V c (v ≫ k)

/-- Independent envelope fullness survives the actual inclusion in the old source. -/
theorem nested_fullEnvelopeInterior_image_le : v.left ''ᵁ U' ≤ U := by
  apply (le_fullEnvelopeInterior_iff f hL d V c k _).mpr
  intro z hz
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨w, hw, hwz⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_prod_fst_with_id v V).map (Over.forget _)) x z hxz
  change π' w = x at hw
  change (prod.map v (𝟙 V)).left w = z at hwz
  have hwU : π' w ∈ U' := by rw [hw]; exact hx
  obtain ⟨r, hr⟩ := fullEnvelopeInterior_full f hL d V c (v ≫ k) hwU
  refine ⟨(nestedToFullRelation f hL d V c k v).left r, ?_⟩
  have hh := congrArg (fun t ↦ t.left r) (nestedToFullRelation_envelope f hL d V c k v)
  change j ((nestedToFullRelation f hL d V c k v).left r) =
    (prod.map v (𝟙 V)).left (j' r) at hh
  rw [hr, hwz] at hh
  exact hh

/-- Restricting to an invariant source open preserves exactly its full-envelope interior. -/
theorem nested_fullEnvelopeInterior_eq
    (hv : p ⁻¹ᵁ v.left.opensRange = q ⁻¹ᵁ v.left.opensRange) : U' = v.left ⁻¹ᵁ U := by
  apply le_antisymm
  · intro x hx
    exact nested_fullEnvelopeInterior_image_le f hL d V c k v ⟨x, hx, rfl⟩
  · apply interior_maximal _ (v.left ⁻¹ᵁ U).isOpen
    intro x hx
    apply nested_fullFiber_retained f hL d V c k v x (interior_subset hx)
    intro z hz
    have hq : q z ∈ v.left.opensRange := ⟨x, hz.symm⟩
    exact (SetLike.ext_iff.mp hv z).mpr hq

end FLT.Mazur.HilbertChart.AffineRestriction
