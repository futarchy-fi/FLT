/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryPicardEtaleTranslation
public import FLT.Mazur.VariableHilbertGeometricOrbitRetention
public import FLT.Mazur.AffineHilbertTranslationRelation

/-!
# Original affine étale-parameter charts through arbitrary geometric classes

Every geometric original Picard class is represented on an original affine
Hilbert chart with affine étale translation parameters. The chart retains
all equal-class geometric maps from its ambient Hilbert scheme. This does
not assert acyclicity for missing translation parameters or full-envelope
membership, and does not assume a global extension of the input class.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ Spec (.of R))
  (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t)))

/-- An arbitrary original geometric class has an affine chart retaining all its ambient lifts. -/
theorem exists_arbitraryPicard_affine_etale_chart :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
      (b : Over.mk t ⟶ A),
      IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      ∃ hk : IsOpenImmersion k.left,
      let _ := hk
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) = s ∧
      ∀ a : Over.mk t ⟶ variableHilbertTest f d V,
        (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) = s →
        ∃! v : Over.mk t ⟶ A, v ≫ k = a := by
  obtain ⟨d, V, c, a, hV, he, ha⟩ := exists_arbitraryPicard_etale_hilbert_lift f hL t s
  obtain ⟨W, hW, _, hret⟩ := exists_affine_retaining_geometric_class f hL d V c a
  let A : Over (Spec (.of R)) := Over.mk (W.ι ≫ (variableHilbertTest f d V).hom)
  let k : A ⟶ variableHilbertTest f d V := Over.homMk W.ι
  let _ : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hf (v : Over.mk t ⟶ variableHilbertTest f d V)
      (hv : (relativeFppfSheaf f).obj.map v.op (variableChartSection f hL d V c) = s) :
      ∃! w : Over.mk t ⟶ A, w ≫ k = v := by
    have hr : Set.range v.left ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      exact hret v (hv.trans ha.symm)
    let w₀ := IsOpenImmersion.lift W.ι v.left hr
    have hw₀ : w₀ ≫ W.ι = v.left := IsOpenImmersion.lift_fac _ _ _
    let w : Over.mk t ⟶ A := Over.homMk w₀ (by
      change w₀ ≫ W.ι ≫ (variableHilbertTest f d V).hom = t
      rw [← Category.assoc, hw₀]
      exact v.w)
    have hw : w ≫ k = v := Over.OverMorphism.ext hw₀
    refine ⟨w, hw, fun w' hw' ↦ ?_⟩
    apply Over.OverMorphism.ext
    exact (cancel_mono k.left).mp (congrArg Over.Hom.left (hw'.trans hw.symm))
  obtain ⟨b, hb, _⟩ := hf a ha
  refine ⟨d, V, c, A, k, b, hV, he, hW, inferInstanceAs (IsOpenImmersion W.ι), ?_, hf⟩
  change (relativeFppfSheaf f).obj.map b.op
    ((relativeFppfSheaf f).obj.map k.op (variableChartSection f hL d V c)) = s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hb]
  exact ha

end FLT.Mazur.HilbertChart.AffineRestriction
