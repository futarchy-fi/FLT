/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationNeighborhoods
public import FLT.Mazur.AffineProductTensorCoordinates

/-!
# Actual tensor envelopes and principal charts of the full Picard relation

The envelope coordinates are the tensor product of the actual source and
translation-base coefficients over R. Their pullback is multiplicative and
retains both original endpoint coordinates. Each pair of complete endpoint
fibers fits in one principal tensor chart inside any prescribed open.
This identifies local tensor charts, not a coaction on the entire envelope.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation AffineProductTensorCoordinates
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "Y" => Over.left (prod A V)
/-- The original structural algebra on source coefficients. -/
local instance sourceCoordinateAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The original structural algebra on translation-base coefficients. -/
local instance translationCoordinateAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom

/-- Pullback of the original tensor-envelope coefficients to the full restricted relation. -/
def tensorCoordinates : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤) →+*
    Γ((relation f hL d V c k).left, ⊤) :=
  (j).appTop.hom.comp (tensorIso A V).hom.hom

/-- Pure tensors retain the original second endpoint and the independent first base coordinate. -/
theorem tensorCoordinates_tmul (a : Γ(A.left, ⊤)) (b : Γ(V.left, ⊤)) :
    tensorCoordinates f hL d V c k (a ⊗ₜ[R] b) =
      (q).left.appTop a * (p ≫ k ≫ variableHilbertBase f d V).left.appTop b := by
  change (j).appTop ((tensorIso A V).hom (a ⊗ₜ[R] b)) = _
  rw [tensorIso_tmul, map_mul]
  congr 1
  exact congrArg (fun g ↦ g.left.appTop b) (toEnvelope_base f hL d V c k)

variable [Etale V.hom] [IsOpenImmersion k.left]

/-- Whole endpoint fibers have a single actual principal tensor chart, with its exact image. -/
theorem exists_tensor_principal_chart (x : A.left)
    (W : (relation f hL d V c k).left.Opens)
    (hW : (p).left ⁻¹' {x} ∪ (q).left ⁻¹' {x} ⊆ W) :
    ∃ (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤))
      (U : (relation f hL d V c k).left.Opens),
      IsAffineOpen U ∧ (p).left ⁻¹' {x} ∪ (q).left ⁻¹' {x} ⊆ U ∧ U ≤ W ∧
        (j) ''ᵁ U = (Y).basicOpen ((tensorIso A V).hom t) := by
  let _ := variableHilbertOverlap_envelope_affine V A
  let F := (p).left ⁻¹' {x} ∪ (q).left ⁻¹' {x}
  have hF : F.Finite :=
    (fst_finite_fiber f hL d V c k x).union (snd_finite_fiber f hL d V c k x)
  obtain ⟨a, ha, haW⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    ((j) ''ᵁ W) ((j) '' F) (hF.image _) (by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, hW hz, rfl⟩)
  have haR : (Y).basicOpen a ≤ (j).opensRange :=
    haW.trans (by rintro _ ⟨z, _, rfl⟩; exact ⟨z, rfl⟩)
  refine ⟨(tensorIso A V).inv a, (j) ⁻¹ᵁ (Y).basicOpen a,
    ((isAffineOpen_top Y).basicOpen a).preimage_of_isOpenImmersion j haR,
    (fun z hz ↦ ha (Set.mem_image_of_mem j hz)), ?_, ?_⟩
  · rw [← (j).preimage_image_eq W]
    exact (TopologicalSpace.Opens.map (j).base).monotone haW
  · rw [Iso.inv_hom_id_apply, Scheme.Hom.image_preimage_eq_opensRange_inf,
      inf_eq_right.mpr haR]

end FLT.Mazur.HilbertChart.AffineRestriction
