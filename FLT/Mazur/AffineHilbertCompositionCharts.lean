/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertComposableEnvelope
public import FLT.Mazur.AffineHilbertPrincipalTensorModel

/-!
# Composition-compatible neighborhoods in the original full relation

A finite set of actual composable pairs, its two arrows and its composites
fit into one principal tensor relation chart and one affine composable chart.
The construction does not assert that this relation chart is closed under
all compositions, or that the source has an invariant affine neighborhood.
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
  [IsOpenImmersion k.left]
local notation "Z" => relation f hL d V c k
local notation "C" => composable f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "Y" => Over.left (prod A V)
local notation "a" => Over.Hom.left (pullback.fst q p)
local notation "b" => Over.Hom.left (pullback.snd q p)
local notation "m" =>
  Over.Hom.left (CategoryTheory.EquivalenceRelation.t (equivalence f hL d V c k))
/-- The algebra induced by the original structural morphism. -/
local instance compositionSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original structural morphism. -/
local instance compositionTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom

/-- A finite collection of original arrows has one principal tensor chart. -/
theorem exists_finite_tensor_principal_chart (W : (Z).left.Opens)
    (s : Set (Z).left) (hs : s.Finite) (hsW : s ⊆ W) :
    ∃ (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) (U : (Z).left.Opens),
      IsAffineOpen U ∧ s ⊆ U ∧ U ≤ W ∧
        (j) ''ᵁ U = (Y).basicOpen ((tensorIso A V).hom t) := by
  let _ := variableHilbertOverlap_envelope_affine V A
  obtain ⟨r, hr, hrW⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    ((j) ''ᵁ W) ((j) '' s) (hs.image _) (by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, hsW hz, rfl⟩)
  have hrR : (Y).basicOpen r ≤ (j).opensRange :=
    hrW.trans (by rintro _ ⟨z, _, rfl⟩; exact ⟨z, rfl⟩)
  refine ⟨(tensorIso A V).inv r, (j) ⁻¹ᵁ (Y).basicOpen r,
    ((isAffineOpen_top Y).basicOpen r).preimage_of_isOpenImmersion j hrR,
    (fun z hz ↦ hr (Set.mem_image_of_mem j hz)), ?_, ?_⟩
  · rw [← (j).preimage_image_eq W]
    exact (TopologicalSpace.Opens.map (j).base).monotone hrW
  · rw [Iso.inv_hom_id_apply, Scheme.Hom.image_preimage_eq_opensRange_inf,
      inf_eq_right.mpr hrR]

/-- The two original arrows and their actual composite, for a collection of pairs. -/
def compositionImages (s : Set (C).left) : Set (Z).left := (a) '' s ∪ (b) '' s ∪ (m) '' s

omit [IsAffine A.left] [IsAffine V.left] [IsOpenImmersion k.left] in
/-- A finite collection of composition diagrams has finitely many original relation arrows. -/
theorem compositionImages_finite (s : Set (C).left) (hs : s.Finite) :
    (compositionImages f hL d V c k s).Finite :=
  ((hs.image _).union (hs.image _)).union (hs.image _)

/-- The maximal domain where both arrows and their composite lie in the chosen relation chart. -/
def compositionDomain (U : (Z).left.Opens) : (C).left.Opens :=
  ((a) ⁻¹ᵁ U ⊓ (b) ⁻¹ᵁ U) ⊓ (m) ⁻¹ᵁ U

omit [IsAffine A.left] [IsAffine V.left] [IsOpenImmersion k.left] in
/-- Controlling the three images is exactly the composition-domain condition. -/
theorem subset_compositionDomain_iff (s : Set (C).left) (U : (Z).left.Opens) :
    s ⊆ compositionDomain f hL d V c k U ↔ compositionImages f hL d V c k s ⊆ U := by
  constructor
  · intro h z hz
    rcases hz with (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩
    · exact (h hx).1.1
    · exact (h hx).1.2
    · exact (h hx).2
  · intro h x hx
    exact ⟨⟨h (Or.inl (Or.inl ⟨x, hx, rfl⟩)),
      h (Or.inl (Or.inr ⟨x, hx, rfl⟩))⟩, h (Or.inr ⟨x, hx, rfl⟩)⟩

/-- A whole finite composition diagram fits in compatible affine and literal tensor charts. -/
theorem exists_composition_charts (s : Set (C).left) (hs : s.Finite)
    (W : (Z).left.Opens) (hsW : compositionImages f hL d V c k s ⊆ W)
    (D : (C).left.Opens) (hsD : s ⊆ D) :
    ∃ (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) (U : (Z).left.Opens) (B : (C).left.Opens),
      IsAffineOpen U ∧ compositionImages f hL d V c k s ⊆ U ∧ U ≤ W ∧
        IsAffineOpen B ∧ s ⊆ B ∧ B ≤ D ∧
        B ≤ compositionDomain f hL d V c k U ∧
        ∃ e : U.toScheme ≅ Spec (.of (Localization.Away t)),
          e.hom ≫ PrincipalLocalizationSquare.inclusion t = U.ι ≫ j ≫ tensorSpectrumMap V := by
  obtain ⟨t, U, hU, hsU, hUW, htU⟩ := exists_finite_tensor_principal_chart
    f hL d V c k W _ (compositionImages_finite f hL d V c k s hs) hsW
  have hDom := (subset_compositionDomain_iff f hL d V c k s U).mpr hsU
  obtain ⟨B, hB, hsB, hBD⟩ := exists_composable_affine_neighborhood f hL d V c k
    (D ⊓ compositionDomain f hL d V c k U) s hs (fun x hx ↦ ⟨hsD hx, hDom hx⟩)
  exact ⟨t, U, B, hU, hsU, hUW, hB, hsB, hBD.trans inf_le_left,
    hBD.trans inf_le_right, principalTensorIso f hL d V c k t U htU,
    principalTensorIso_inclusion f hL d V c k t U htU⟩

end FLT.Mazur.HilbertChart.AffineRestriction
