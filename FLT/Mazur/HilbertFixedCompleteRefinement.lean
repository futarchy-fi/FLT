/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteInteriorCharts
public import FLT.Mazur.EquivalenceRelationFixedFrameInterior

/-!
# Complete affine refinements inside a prescribed stable chart

The original fixed size and distinguished label are retained. An interior
complete point supplies a stable affine subchart of any prescribed stable
open containing it. The domain need not be the chart's own orbit image.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
variable (n : ℕ) (o : Fin n)
  (B : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hB : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ B = B)
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence

include hB

/-- Refine the prescribed original chart at an interior complete point, keeping its labels. -/
theorem exists_fixed_complete_affine_refinement
    (x : normalizedFullRelationFrames f hL d V c k n o) (hx : x ∈ B)
    (hc : x ∈ completeInterior («p» := p) («q» := q) (Fin n) o) :
    ∃ (U : (normalizedFullRelationFrames f hL d V c k n o).Opens),
      (∀ σ : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U) ∧
      U ≤ B ∧ IsAffineOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) := by
  let Q := completeInterior («p» := p) («q» := q) (Fin n) o ⊓ B
  have hQ : ∀ σ : Equiv.Perm (Fin n),
      (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ Q = Q := by
    intro σ
    change (action e (Fin n) o σ).hom ⁻¹ᵁ
      (completeInterior (Fin n) o ⊓ B) = _
    rw [Scheme.Hom.preimage_inf, completeInterior_action_invariant]
    rw [show (action e (Fin n) o σ).hom ⁻¹ᵁ B = B from hB σ]
  obtain ⟨U, ha, hxU, hUQ, hU, _⟩ :=
    exists_normalized_affine_refinement f hL d V c k n o Q hQ x ⟨hc, hx⟩
  refine ⟨U, hU, hUQ.trans inf_le_right, ha, hxU, ?_⟩
  intro y hy
  exact completeInterior_subset (Fin n) o (hUQ hy).1

/-- The exact prescribed geometric map factors through a complete affine subchart. -/
theorem exists_fixed_complete_geometric_refinement {K : Type} [Field K]
    (v : Spec (.of K) ⟶ B.toScheme)
    (hc : (v ≫ B.ι) default ∈ completeInterior («p» := p) («q» := q) (Fin n) o) :
    ∃ (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (_hU : ∀ σ : Equiv.Perm (Fin n),
        (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
      (_hUB : U ≤ B) (z : Spec (.of K) ⟶ U.toScheme),
      IsAffineOpen U ∧ z ≫ U.ι = v ≫ B.ι ∧
      ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o := by
  obtain ⟨U, hU, hUB, ha, hx, hC⟩ :=
    exists_fixed_complete_affine_refinement f hL d V c k n o B hB
      ((v ≫ B.ι) default) (v default).property hc
  have hr : Set.range (v ≫ B.ι) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    rw [Subsingleton.elim t default]
    exact hx
  exact ⟨U, hU, hUB, IsOpenImmersion.lift U.ι (v ≫ B.ι) hr, ha,
    IsOpenImmersion.lift_fac _ _ _, hC⟩

end FLT.Mazur.HilbertChart.AffineRestriction
