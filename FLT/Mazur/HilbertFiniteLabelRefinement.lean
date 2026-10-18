/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationLabelOpenCharts
public import FLT.Mazur.HilbertNormalizedAffineRefinement

/-!
# Common affine refinements of finite independently labelled chart families

At every point belonging to all transported chart domains, a stable affine
chart refines the entire finite family. Transporting it back gives coherent
subcharts inside every supplied domain. The construction retains each label.
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

/-- Finite families of labelled stable charts have common affine refinements at overlap points. -/
theorem exists_normalized_finite_label_refinement (n : ℕ) (o : Fin n)
    (E : A.left.Opens) (hE : (p) ⁻¹ᵁ E = (q) ⁻¹ᵁ E)
    {T : Type} [Finite T] (a : T → Fin n)
    (Us : (v : T) → (normalizedFullRelationFrames f hL d V c k n (a v)).Opens)
    (hUs : ∀ v σ,
      (normalizedFullRelationAction f hL d V c k n (a v) σ).hom ⁻¹ᵁ Us v = Us v)
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hxE : normalizedFullRelationFirst f hL d V c k n o x ∈ E)
    (hx : ∀ v, labelChange e (Fin n) o (a v) x ∈ Us v) :
    ∃ Z : (normalizedFullRelationFrames f hL d V c k n o).Opens,
      IsAffineOpen Z ∧ x ∈ Z ∧
      Z ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E ∧
      (∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ Z = Z) ∧
      ∀ v, labelChange e (Fin n) (a v) o ⁻¹ᵁ Z ≤ Us v := by
  let O : (normalizedFullRelationFrames f hL d V c k n o).Opens :=
    ⨅ v, labelChange e (Fin n) o (a v) ⁻¹ᵁ Us v
  have hO : ∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ O = O := by
    intro σ
    apply SetLike.ext
    intro y
    change (normalizedFullRelationAction f hL d V c k n o σ).hom y ∈ O ↔ y ∈ O
    simp only [O, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    apply forall_congr'
    intro v
    exact SetLike.ext_iff.mp
      (label_preimage_stable e (Fin n) o (a v) (Us v) (hUs v) σ) y
  have hxO : x ∈ O := by
    change x ∈ (O : Set _)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun v ↦ (Scheme.Hom.mem_preimage _).mpr (hx v)
  let W := (normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E) ⊓ O
  have hW : ∀ σ, (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ W = W := by
    intro σ
    dsimp only [W]
    rw [Scheme.Hom.preimage_inf, hO σ]
    exact congrArg (fun Q ↦ Q ⊓ O) (first_preimage_stable e (Fin n) o E hE σ)
  obtain ⟨Z, ha, hxZ, hZW, hZ, _⟩ :=
    exists_normalized_affine_refinement f hL d V c k n o W hW x ⟨hxE, hxO⟩
  refine ⟨Z, ha, hxZ, hZW.trans inf_le_left, hZ, fun v ↦ ?_⟩
  have hv := (labelChange e (Fin n) (a v) o).preimage_mono
    ((hZW.trans inf_le_right).trans (iInf_le _ v))
  simpa only [← Scheme.Hom.comp_preimage, labelChange_comp, labelChange_self,
    Scheme.Hom.id_preimage] using hv

end FLT.Mazur.HilbertChart.AffineRestriction
