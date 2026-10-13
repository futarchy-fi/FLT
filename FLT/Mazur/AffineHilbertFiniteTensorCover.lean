/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation
public import FLT.Mazur.AffineHilbertTensorAtlas

/-!
# Finitely many literal tensor charts detect the full Hilbert relation

Noetherianity of the original relation supplies a finite selection of the
actual principal tensor charts. Every arrow is covered, and the full original
invariant condition is exactly the finite family of localized tensor equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation AffineProductTensorCoordinates
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
/-- Original coefficient algebra on the selected parameter source. -/
local instance finiteTensorSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- Original coefficient algebra on the selected translation. -/
local instance finiteTensorTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom

/-- Finitely many original tensor charts jointly cover every original relation point. -/
theorem exists_finite_tensor_cover : ∃ t : Finset (TensorChart f hL d V c k),
    ∀ x : (D).left, ∃ T ∈ t, x ∈ T.domain := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun T : TensorChart f hL d V c k ↦ (T.domain : Set (D).left))
    (fun T ↦ T.domain.isOpen) (by
    intro x _
    obtain ⟨T, hx, _⟩ := TensorChart.exists_mem f hL d V c k x ⊤ trivial
    exact Set.mem_iUnion.mpr ⟨T, hx⟩)
  refine ⟨t, fun x ↦ ?_⟩
  obtain ⟨T, hT, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨T, hT, hx⟩

/-- A finite set of labels from the actual principal tensor atlas. -/
def finiteTensorLabels : Finset (TensorChart f hL d V c k) :=
  (exists_finite_tensor_cover f hL d V c k).choose

/-- Every original arrow is in a selected tensor chart. -/
theorem finiteTensorLabels_covers (x : (D).left) :
    ∃ T : finiteTensorLabels f hL d V c k, x ∈ T.val.domain := by
  obtain ⟨T, hT, hx⟩ := (exists_finite_tensor_cover f hL d V c k).choose_spec x
  exact ⟨⟨T, hT⟩, hx⟩

/-- The finitely many selected original tensor charts form an actual scheme open cover. -/
def finiteTensorCover : (D).left.OpenCover where
  I₀ := finiteTensorLabels f hL d V c k
  X T := T.val.domain.toScheme
  f T := T.val.domain.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun _ ↦ inferInstance⟩
    obtain ⟨T, hx⟩ := finiteTensorLabels_covers f hL d V c k x
    exact ⟨T, ⟨x, hx⟩, rfl⟩

instance : Finite (finiteTensorCover f hL d V c k).I₀ :=
  inferInstanceAs (Finite (finiteTensorLabels f hL d V c k))

instance (i : (finiteTensorCover f hL d V c k).I₀) :
    IsAffine ((finiteTensorCover f hL d V c k).X i) :=
  TensorChart.isAffine f hL d V c k i.val

/-- Full invariance is detected by the finite set of actual literal tensor equations. -/
theorem original_invariant_iff_finite_tensor_equations (a : Γ(A.left, ⊤)) :
    (p).left.appTop a = (q).left.appTop a ↔
      ∀ T : finiteTensorLabels f hL d V c k,
        localizedSourceMap f hL d V c k T.val.denominator T.val.domain T.val.image_eq a =
          algebraMap _ (Localization.Away T.val.denominator)
            (a ⊗ₜ[R] (1 : Γ(V.left, ⊤))) := by
  constructor
  · intro h T
    exact (original_invariant_iff_tensor_equations f hL d V c k a).mp h
      T.val.denominator T.val.domain T.val.image_eq
  · intro h
    apply TopCat.Presheaf.IsSheaf.section_ext (D).left.IsSheaf
    intro x _
    obtain ⟨T, hx⟩ := finiteTensorLabels_covers f hL d V c k x
    refine ⟨T.val.domain.ι ''ᵁ ⊤, le_top, ⟨⟨x, hx⟩, trivial, rfl⟩, ?_⟩
    apply (TensorChart.sectionsIso f hL d V c k T.val).commRingCatIsoToRingEquiv.injective
    exact (h T).trans (localizedTestMap_eq_localization
      f hL d V c k T.val.denominator T.val.domain T.val.image_eq a).symm

end FLT.Mazur.HilbertChart.AffineRestriction
