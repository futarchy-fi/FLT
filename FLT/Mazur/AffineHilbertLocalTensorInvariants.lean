/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertCompositionCharts
public import FLT.Mazur.AffineHilbertLocalizedTensorFormula

/-!
# Full original invariants detected by literal local tensor equations

The principal tensor charts cover the entire original relation. Equality of
the actual endpoint pullbacks is therefore equivalent to the explicit source
coefficient equation in every literal localization of the tensor envelope.
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
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
/-- The algebra induced by the original source structural morphism. -/
local instance invariantSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original translation structural morphism. -/
local instance invariantTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom

/-- Every original relation point belongs to a principal tensor chart inside any neighborhood. -/
theorem exists_point_tensor_chart (x : (Z).left) (W : (Z).left.Opens) (hx : x ∈ W) :
    ∃ (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) (U : (Z).left.Opens),
      IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧
        (toEnvelope f hL d V c k).left ''ᵁ U =
          (prod A V).left.basicOpen ((tensorIso A V).hom t) := by
  obtain ⟨t, U, hU, hxU, hUW, htU⟩ := exists_finite_tensor_principal_chart
    f hL d V c k W {x} (Set.finite_singleton x) (Set.singleton_subset_iff.mpr hx)
  exact ⟨t, U, hU, hxU (Set.mem_singleton x), hUW, htU⟩

/-- The entire original relation equation is detected on its actual principal tensor charts. -/
theorem original_invariant_iff_localized (a : Γ(A.left, ⊤)) :
    (p).left.appTop a = (q).left.appTop a ↔
      ∀ (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) (U : (Z).left.Opens)
        (hU : (toEnvelope f hL d V c k).left ''ᵁ U =
          (prod A V).left.basicOpen ((tensorIso A V).hom t)),
        localizedSourceMap f hL d V c k t U hU a =
          localizedTestMap f hL d V c k t U hU a := by
  constructor
  · intro h t U hU
    exact congrArg (fun z ↦ (principalTensorSectionsIso f hL d V c k t U hU).hom
      (U.ι.appTop z)) h
  · intro h
    apply TopCat.Presheaf.IsSheaf.section_ext (Z).left.IsSheaf
    intro x _
    obtain ⟨t, U, _, hxU, _, htU⟩ := exists_point_tensor_chart f hL d V c k x ⊤ trivial
    refine ⟨U.ι ''ᵁ ⊤, le_top, ⟨⟨x, hxU⟩, trivial, rfl⟩, ?_⟩
    exact (principalTensorSectionsIso f hL d V c k t U htU).commRingCatIsoToRingEquiv.injective
      (h t U htU)

/-- Full original invariance is exactly the literal localized source/tensor-unit equation. -/
theorem original_invariant_iff_tensor_equations (a : Γ(A.left, ⊤)) :
    (p).left.appTop a = (q).left.appTop a ↔
      ∀ (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) (U : (Z).left.Opens)
        (hU : (toEnvelope f hL d V c k).left ''ᵁ U =
          (prod A V).left.basicOpen ((tensorIso A V).hom t)),
        localizedSourceMap f hL d V c k t U hU a =
          algebraMap _ (Localization.Away t) (a ⊗ₜ[R] (1 : Γ(V.left, ⊤))) := by
  rw [original_invariant_iff_localized]
  simp only [localizedTestMap_eq_localization]

end FLT.Mazur.HilbertChart.AffineRestriction
