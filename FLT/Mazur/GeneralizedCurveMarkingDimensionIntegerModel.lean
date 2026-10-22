/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientDimensionMarkingRefinement
public import FLT.Mazur.GeneralizedCurveMarkingSmoothIntegerModel
public import FLT.Mazur.GeneralizedCurveSmoothOpenDimension

/-!
# Noetherian marked models with a relative-curve neighborhood

The actual whole family over an arbitrary ring has a proper Noetherian
model with its entire marking in a relative-dimension-one open. Any chosen
original pole line still recovers along the same Cartesian square.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open Approximation FCurve SectionCoverBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Finite integer coefficients retain dimension one around the whole original marking. -/
theorem exists_smoothMarking_dimension_integer_model {A : Type} [CommRing A]
    (E : GeneralizedEllipticCurve (Spec (.of A)))
    (s : 𝟙_ (Over (Spec (.of A))) ⟶ E.group) (m : ℕ)
    (c₀ : Set A) (hc₀ : c₀.Finite) :
    ∃ (R : Subalgebra ℤ A) (_ : Algebra.FiniteType ℤ R) (_ : c₀ ⊆ R)
      (Y : Scheme) (q : Y ⟶ Spec (.of R)) (M : Y.Modules)
      (t : Spec (.of R) ⟶ Y) (f : E.curve.left ⟶ Y) (V : Y.Opens),
      IsProper q ∧ LocallyOfFinitePresentation q ∧ IsNoetherian Y ∧
        LocallyFreeRankOne M ∧ IsClosedImmersion t ∧ t ≫ q = 𝟙 _ ∧
        IsPullback f E.curve.hom q (Spec.map (CommRingCat.ofHom R.val.toRingHom)) ∧
        t ⁻¹ᵁ V = ⊤ ∧ SmoothOfRelativeDimension 1 (V.ι ≫ q) ∧
        Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t = (s ≫ E.inclusion).left ≫ f ∧
        Nonempty ((Scheme.Modules.pullback f).obj M ≅ E.smoothMarkingPower s m) := by
  obtain ⟨R, hR, hcR, Y, p, M, t, a, hp, hfp, _, hM, _, ht, ha, hsm, he, ⟨e⟩⟩ :=
    E.exists_smoothMarking_smooth_integer_model s m c₀ hc₀
  have hW := (isPullback_morphismRestrict a p.smoothLocus).paste_vert ha
  have : Smooth (p.smoothLocus.ι ≫ p) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact p.smoothLocus.ι_preimage_self
  have : Smooth ((a ⁻¹ᵁ p.smoothLocus).ι ≫ E.curve.hom) :=
    MorphismProperty.of_isPullback hW inferInstance
  let _ := E.smooth_open_relativeDimension (a ⁻¹ᵁ p.smoothLocus)
  obtain ⟨i, V, hV, hd, hei⟩ := exists_coefficient_dimension_marking R p ha
    (s ≫ E.inclusion).left (s ≫ E.inclusion).w t ht he hsm 1
  let B := i.unop.val
  let _ : Algebra.FiniteType ℤ B := i.unop.property.2
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  let b : Spec (.of B) ⟶ Spec (.of R) := (coefficientSpectrumToInitial R).app i
  let q := pullback.snd p b
  let f := coefficientModelRecovery ha i
  let c := pullback.fst p b
  let ti := sectionMap p b t ht
  have hti := sectionMap_snd p b t ht
  let _ : IsLocallyNoetherian (pullback p b) := LocallyOfFiniteType.isLocallyNoetherian q
  let _ : CompactSpace ↥(pullback p b) := QuasiCompact.compactSpace_of_compactSpace q
  have hclosed : IsClosedImmersion ti := by
    have : IsClosedImmersion (ti ≫ q) := by rw [hti]; infer_instance
    exact IsClosedImmersion.of_comp ti q
  refine ⟨B, inferInstance, fun x hx ↦ i.unop.property.1 (hcR hx), _, q,
    (Scheme.Modules.pullback c).obj M, ti, f, V, inferInstance, inferInstance,
    ⟨⟩, hM.pullback c, hclosed, hti, coefficientModelRecovery_isPullback ha i,
    hV, hd, hei, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp f c).app M ≪≫
    (Scheme.Modules.pullbackCongr (coefficientModelRecovery_fst ha i)).app M ≪≫ e

end FLT.Mazur.GeneralizedEllipticCurve
