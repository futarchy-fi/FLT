/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeOpenCharts
public import FLT.Mazur.HilbertNormalizedAffineRefinement

/-!
# Affine domains retaining every embedding into independent smaller charts

At a point where all specified subframes land, construct a stable affine
neighborhood inside their simultaneous domains and the original larger chart.
Sizes and distinguished labels vary independently throughout the finite family.
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

/-- Construct a stable affine neighborhood retaining all unequal-size subframe selections. -/
theorem exists_normalized_finite_subframe_refinement (n : ℕ) (o : Fin n)
    (E : A.left.Opens) (hE : (p) ⁻¹ᵁ E = (q) ⁻¹ᵁ E)
    (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
    (hU : ∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
    {T : Type} [Finite T] (m : T → ℕ) (a : ∀ v, Fin (m v))
    (Us : (v : T) → (normalizedFullRelationFrames f hL d V c k (m v) (a v)).Opens)
    (x : normalizedFullRelationFrames f hL d V c k n o) (hxU : x ∈ U)
    (hxE : normalizedFullRelationFirst f hL d V c k n o x ∈ E)
    (hx : ∀ v (ι : Fin (m v) ↪ Fin n), subframeMap e o (a v) ι x ∈ Us v) :
    ∃ Z : (normalizedFullRelationFrames f hL d V c k n o).Opens,
      IsAffineOpen Z ∧ x ∈ Z ∧ Z ≤ U ∧
      Z ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E ∧
      (∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ Z = Z) ∧
      ∀ v (ι : Fin (m v) ↪ Fin n), Z ≤ subframeMap e o (a v) ι ⁻¹ᵁ Us v := by
  let O : (normalizedFullRelationFrames f hL d V c k n o).Opens :=
    ⨅ v, allSubframeOpen e o (a v) (Us v)
  have hO : ∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ O = O := by
    intro σ
    apply SetLike.ext
    intro y
    change (normalizedFullRelationAction f hL d V c k n o σ).hom y ∈ O ↔ y ∈ O
    simp only [O, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    apply forall_congr'
    intro v
    exact SetLike.ext_iff.mp (allSubframeOpen_stable e o (a v) (Us v) σ) y
  have hxO : x ∈ O := by
    change x ∈ (O : Set _)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun v ↦ (mem_allSubframeOpen e o (a v) (Us v) x).mpr (hx v)
  let W := U ⊓ ((normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E) ⊓ O)
  have hW : ∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ W = W := by
    intro σ
    dsimp only [W]
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, hU σ, hO σ]
    exact congrArg (fun Q ↦ U ⊓ (Q ⊓ O)) (first_preimage_stable e (Fin n) o E hE σ)
  obtain ⟨Z, ha, hxZ, hZW, hZ, _⟩ :=
    exists_normalized_affine_refinement f hL d V c k n o W hW x ⟨hxU, hxE, hxO⟩
  refine ⟨Z, ha, hxZ, hZW.trans inf_le_left,
    hZW.trans (inf_le_right.trans inf_le_left), hZ, fun v ι ↦ ?_⟩
  exact (hZW.trans (inf_le_right.trans inf_le_right)).trans
    ((iInf_le _ v).trans (allSubframeOpen_le e o (a v) (Us v) ι))

end FLT.Mazur.HilbertChart.AffineRestriction
