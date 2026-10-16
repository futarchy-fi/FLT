/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedRelationComparison
public import FLT.Mazur.HilbertOrderedAffineEnvelope
public import FLT.Mazur.FiniteGroupClosedEnvelopeNeighborhood

/-!
# Affine source neighborhoods for the moving normalized Hilbert action

Normalized frames form a closed subscheme of the original ordered-frame scheme,
which has an actual open affine envelope. Every normalized permutation orbit
therefore lies in a stable affine source open. The first endpoint is etale.
Completeness throughout these neighborhoods is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  (n : ℕ) (o : Fin n)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedFullRelationAction f hL d V c k n o

/-- Normalization embeds as the exact closed endpoint equalizer in the original frame scheme. -/
def normalizedOriginalFrameInclusion : N ⟶ (fullRelationOrderedPoints f hL d V c k n).left :=
  inclusion p q (Fin n) o

instance normalizedOriginalFrameInclusion_closed :
    IsClosedImmersion (normalizedOriginalFrameInclusion f hL d V c k n o) := by
  change IsClosedImmersion (equalizer.ι _ _)
  infer_instance

omit [Etale V.hom] in
/-- A finite stable set has an actual affine neighborhood for the moving original action. -/
theorem exists_normalized_stable_affine_set (s : Set N) (hs : s.Finite)
    (hi : ∀ σ : Equiv.Perm (Fin n), (ρ σ).hom '' s ⊆ s) :
    ∃ U : (N).Opens, IsAffineOpen U ∧ s ⊆ U ∧
      ∀ σ : Equiv.Perm (Fin n), (ρ σ).hom ⁻¹ᵁ U = U := by
  let _ := RelativeOrderedTuples.finTuples_affine (firstRelationEnvelope (A := A) V) n
  exact FiniteGroupNeighborhood.exists_closed_envelope_stable_affine ρ
    (normalizedOriginalFrameInclusion f hL d V c k n o)
    (fullRelationOrderedEnvelopeMap f hL d V c k n) s hs hi

/-- Every original normalized source point has a stable affine etale source neighborhood. -/
theorem exists_normalized_stable_affine (x : N) :
    ∃ U : (N).Opens, IsAffineOpen U ∧ x ∈ U ∧
      (∀ σ : Equiv.Perm (Fin n), (ρ σ).hom ⁻¹ᵁ U = U) ∧
      Etale (U.ι ≫ normalizedFullRelationFirst f hL d V c k n o) := by
  let _ := RelativeOrderedTuples.finTuples_affine (firstRelationEnvelope (A := A) V) n
  obtain ⟨U, hU, hx, hρ⟩ := FiniteGroupNeighborhood.exists_closed_envelope_orbit_affine ρ
    (normalizedOriginalFrameInclusion f hL d V c k n o)
    (fullRelationOrderedEnvelopeMap f hL d V c k n) x
  exact ⟨U, hU, hx, hρ, inferInstance⟩

/-- Every geometric normalized frame factors through an actual stable affine source open. -/
theorem exists_normalized_stable_affine_test {K : Type} [Field K]
    (a : Spec (.of K) ⟶ N) :
    ∃ (U : (N).Opens) (v : Spec (.of K) ⟶ U.toScheme), IsAffineOpen U ∧
      (∀ σ : Equiv.Perm (Fin n), (ρ σ).hom ⁻¹ᵁ U = U) ∧ v ≫ U.ι = a ∧
      Etale (U.ι ≫ normalizedFullRelationFirst f hL d V c k n o) := by
  obtain ⟨U, hU, hx, hρ, he⟩ := exists_normalized_stable_affine f hL d V c k n o (a default)
  have ha : Set.range a ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change a x ∈ U
    rw [Subsingleton.elim x default]
    exact hx
  exact ⟨U, IsOpenImmersion.lift U.ι a ha, hU, hρ,
    IsOpenImmersion.lift_fac U.ι a ha, he⟩

end FLT.Mazur.HilbertChart.AffineRestriction
