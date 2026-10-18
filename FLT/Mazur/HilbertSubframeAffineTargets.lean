/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeSelectedPoints
public import FLT.Mazur.HilbertFiniteSubframeRefinement

/-!
# Constructing independent affine targets for every selected subframe

The finite set of all selected images has a stable affine neighborhood inside
any prescribed original invariant domain. For a finite family of target sizes,
construct these targets independently and shrink the source to a common stable
affine neighborhood retaining every selection into every target.
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
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k

omit [Etale V.hom] in
/-- Every open containing all selected images admits a stable affine target refinement. -/
theorem exists_normalized_subframe_target_refinement (n : ℕ) (o : Fin n)
    (m : ℕ) (a : Fin m)
    (Q : (normalizedFullRelationFrames f hL d V c k m a).Opens)
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hx : ∀ ι : Fin m ↪ Fin n, subframeMap e o a ι x ∈ Q) :
    ∃ T : (normalizedFullRelationFrames f hL d V c k m a).Opens,
      IsAffineOpen T ∧
      (∀ ι : Fin m ↪ Fin n, subframeMap e o a ι x ∈ T) ∧ T ≤ Q ∧
      ∀ σ, (normalizedFullRelationAction f hL d V c k m a σ).hom ⁻¹ᵁ T = T := by
  let _ := RelativeOrderedTuples.finTuples_affine (firstRelationEnvelope (A := A) V) m
  obtain ⟨T, ha, hsT, hTQ, hT⟩ :=
    FiniteGroupNeighborhood.exists_closed_envelope_affine_refinement
      (normalizedFullRelationAction f hL d V c k m a)
      (normalizedOriginalFrameInclusion f hL d V c k m a)
      (fullRelationOrderedEnvelopeMap f hL d V c k m)
      (selectedSubframePoints e o a x) (selectedSubframePoints_finite e o a x)
      (selectedSubframePoints_stable e o a x) Q (by rintro _ ⟨ι, rfl⟩; exact hx ι)
  exact ⟨T, ha, fun ι ↦ hsT ⟨ι, rfl⟩, hTQ, hT⟩

omit [Etale V.hom] in
/-- Construct one affine target containing every selected image of the original point. -/
theorem exists_normalized_subframe_affine_target (n : ℕ) (o : Fin n)
    (m : ℕ) (a : Fin m) (E : A.left.Opens) (hE : (p) ⁻¹ᵁ E = (q) ⁻¹ᵁ E)
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hx : normalizedFullRelationFirst f hL d V c k n o x ∈ E) :
    ∃ T : (normalizedFullRelationFrames f hL d V c k m a).Opens,
      IsAffineOpen T ∧
      (∀ ι : Fin m ↪ Fin n, subframeMap e o a ι x ∈ T) ∧
      T ≤ normalizedFullRelationFirst f hL d V c k m a ⁻¹ᵁ E ∧
      ∀ σ, (normalizedFullRelationAction f hL d V c k m a σ).hom ⁻¹ᵁ T = T := by
  exact exists_normalized_subframe_target_refinement f hL d V c k n o m a
    (normalizedFullRelationFirst f hL d V c k m a ⁻¹ᵁ E) x
    (fun ι ↦ selectedSubframePoints_subset_domain e o a x E hE hx ⟨ι, rfl⟩)

/-- Independently construct all targets and their common stable affine source neighborhood. -/
theorem exists_normalized_subframe_affine_family (n : ℕ) (o : Fin n)
    (E : A.left.Opens) (hE : (p) ⁻¹ᵁ E = (q) ⁻¹ᵁ E)
    (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
    (hU : ∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
    {T : Type} [Finite T] (m : T → ℕ) (a : ∀ v, Fin (m v))
    (x : normalizedFullRelationFrames f hL d V c k n o) (hxU : x ∈ U)
    (hxE : normalizedFullRelationFirst f hL d V c k n o x ∈ E) :
    ∃ Us : (v : T) → (normalizedFullRelationFrames f hL d V c k (m v) (a v)).Opens,
      (∀ v, IsAffineOpen (Us v)) ∧
      (∀ v, Us v ≤ normalizedFullRelationFirst f hL d V c k (m v) (a v) ⁻¹ᵁ E) ∧
      (∀ v σ, (normalizedFullRelationAction f hL d V c k (m v) (a v) σ).hom ⁻¹ᵁ
        Us v = Us v) ∧
      ∃ Z : (normalizedFullRelationFrames f hL d V c k n o).Opens,
        IsAffineOpen Z ∧ x ∈ Z ∧ Z ≤ U ∧
        Z ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E ∧
        (∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ Z = Z) ∧
        ∀ v (ι : Fin (m v) ↪ Fin n), Z ≤ subframeMap e o (a v) ι ⁻¹ᵁ Us v := by
  have ht (v : T) :=
    exists_normalized_subframe_affine_target f hL d V c k n o (m v) (a v) E hE x hxE
  choose Us ha hx hE' hstable using ht
  refine ⟨Us, ha, hE', hstable, ?_⟩
  exact exists_normalized_finite_subframe_refinement f hL d V c k n o E hE U hU
    m a Us x hxU hxE hx

end FLT.Mazur.HilbertChart.AffineRestriction
