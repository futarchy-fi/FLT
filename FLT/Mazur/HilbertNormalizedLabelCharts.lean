/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationLabelOpenCharts
public import FLT.Mazur.HilbertNormalizedAffineRefinement

/-!
# Compatible moving Hilbert source charts for every distinguished label

An actual affine moving chart over an original invariant domain transports
simultaneously to every distinguished label. The resulting affine etale charts
are stable and satisfy exact transition laws. Completeness on them is not asserted.
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

/-- Actual affine moving charts can be chosen coherently for all distinguished labels. -/
theorem exists_normalized_label_chart_family (n : ℕ) (o : Fin n)
    (W : A.left.Opens) (hW : (p) ⁻¹ᵁ W = (q) ⁻¹ᵁ W)
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hx : normalizedFullRelationFirst f hL d V c k n o x ∈ W) :
    ∃ U : (o' : Fin n) → (normalizedFullRelationFrames f hL d V c k n o').Opens,
      x ∈ U o ∧
      (∀ o', IsAffineOpen (U o')) ∧
      (∀ o' σ, (normalizedFullRelationAction f hL d V c k n o' σ).hom ⁻¹ᵁ U o' = U o') ∧
      (∀ o', U o' ≤ normalizedFullRelationFirst f hL d V c k n o' ⁻¹ᵁ W) ∧
      (∀ o', Etale ((U o').ι ≫ normalizedFullRelationFirst f hL d V c k n o')) ∧
      ∀ o₁ o₂, labelChange e (Fin n) o₁ o₂ ⁻¹ᵁ U o₂ = U o₁ := by
  obtain ⟨U, ha, hxU, hUW, hU, _⟩ :=
    exists_normalized_affine_original_domain f hL d V c k n o W hW x hx
  refine ⟨fun o' ↦ labelChange e (Fin n) o' o ⁻¹ᵁ U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [labelChange_self, Scheme.Hom.id_preimage] using hxU
  · intro o'
    exact label_preimage_affine e (Fin n) o' o U ha
  · intro o' σ
    exact label_preimage_stable e (Fin n) o' o U hU σ
  · intro o'
    exact label_preimage_domain e (Fin n) o' o U W hW hUW
  · intro o'
    infer_instance
  · intro o₁ o₂
    rw [← Scheme.Hom.comp_preimage, labelChange_comp]

end FLT.Mazur.HilbertChart.AffineRestriction
