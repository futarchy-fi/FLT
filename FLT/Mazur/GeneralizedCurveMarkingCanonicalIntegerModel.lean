/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingDimensionIntegerModel
public import FLT.Mazur.SmoothMarkingNeighborhoodCartier

/-!
# Canonical marked divisor lines on actual finite integer models

The finite model's own marking is relative Cartier. Its canonical line and
vanishing section recover the original ones, and all original pole powers
recover on this single model. No unrelated model line is chosen.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open Approximation FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- One proper Noetherian marked model recovers the canonical section and every pole power. -/
theorem exists_smoothMarking_canonical_integer_model {A : Type} [CommRing A]
    (E : GeneralizedEllipticCurve (Spec (.of A)))
    (s : 𝟙_ (Over (Spec (.of A))) ⟶ E.group) (c₀ : Set A) (hc₀ : c₀.Finite) :
    ∃ (R : Subalgebra ℤ A) (_ : Algebra.FiniteType ℤ R) (_ : c₀ ⊆ R)
      (Y : Scheme) (q : Y ⟶ Spec (.of R))
      (t : Spec (.of R) ⟶ Y) (f : E.curve.left ⟶ Y) (V : Y.Opens),
      IsProper q ∧ LocallyOfFinitePresentation q ∧ IsNoetherian Y ∧
        IsClosedImmersion t ∧ t ≫ q = 𝟙 _ ∧
        IsPullback f E.curve.hom q (Spec.map (CommRingCat.ofHom R.val.toRingHom)) ∧
        t ⁻¹ᵁ V = ⊤ ∧ SmoothOfRelativeDimension 1 (V.ι ≫ q) ∧
        Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t = (s ≫ E.inclusion).left ≫ f ∧
        ∃ hI : RelativeEffectiveCartier q t.ker,
          (∀ m : ℕ, Nonempty ((pullback f).obj (tensorPower (divisorLineBundle t.ker hI.1) m)
            ≅ E.smoothMarkingPower s m)) ∧
          ∃ e : (pullback f).obj (divisorLineBundle t.ker hI.1) ≅
              divisorLineBundle (s ≫ E.inclusion).left.ker (E.smoothMarking_relativeCartier s).1,
            (pullback f).map (divisorSectionMap hI.1) ≫ e.hom =
              (modulePullbackUnitIso f).hom ≫
                divisorSectionMap (E.smoothMarking_relativeCartier s).1 := by
  obtain ⟨R, hR, hcR, Y, q, _, t, f, V, hp, hfp, hY, _, htcl, ht, hf, hV, hd, he, _⟩ :=
    E.exists_smoothMarking_dimension_integer_model s 0 c₀ hc₀
  have hI := relativeCartier_of_section_neighborhood q t ht V hV
  refine ⟨R, hR, hcR, Y, q, t, f, V, hp, hfp, hY, htcl, ht, hf, hV, hd, he,
    hI, fun m ↦ ⟨?_⟩, ?_⟩
  · exact sectionPointPowerIso hf t (s ≫ E.inclusion).left ht (s ≫ E.inclusion).w
      he.symm hI.1 (E.smoothMarking_relativeCartier s).1 m
  · exact ⟨sectionPointLineIso hf t (s ≫ E.inclusion).left ht (s ≫ E.inclusion).w
      he.symm hI.1 (E.smoothMarking_relativeCartier s).1,
      sectionPointLineIso_section hf t (s ≫ E.inclusion).left ht (s ≫ E.inclusion).w
        he.symm hI.1 (E.smoothMarking_relativeCartier s).1⟩

end FLT.Mazur.GeneralizedEllipticCurve
