/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientSmoothMarkingRefinement
public import FLT.Mazur.GeneralizedCurveMarkingIntegerModel
public import FLT.Mazur.SmoothSectionCompactNeighborhood

/-!
# Noetherian models retaining the original smooth marking

The original whole family over an arbitrary ring has a proper Noetherian
model whose marking lies in the relative smooth locus. Its original pole
line recovers along the same Cartesian square. This does not yet assert
flatness or classified genus-one geometric fibers for the model.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open Approximation FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The original marking remains smooth on a proper Noetherian whole-family model. -/
theorem exists_smoothMarking_smooth_integer_model {A : Type} [CommRing A]
    (E : GeneralizedEllipticCurve (Spec (.of A)))
    (s : 𝟙_ (Over (Spec (.of A))) ⟶ E.group) (m : ℕ)
    (c₀ : Set A) (hc₀ : c₀.Finite) :
    ∃ (R : Subalgebra ℤ A) (_ : Algebra.FiniteType ℤ R) (_ : c₀ ⊆ R)
      (Y : Scheme) (q : Y ⟶ Spec (.of R)) (M : Y.Modules)
      (t : Spec (.of R) ⟶ Y) (f : E.curve.left ⟶ Y),
      ∃ (_ : IsProper q) (_ : LocallyOfFinitePresentation q),
        IsNoetherian Y ∧ LocallyFreeRankOne M ∧ IsClosedImmersion t ∧ t ≫ q = 𝟙 _ ∧
        IsPullback f E.curve.hom q (Spec.map (CommRingCat.ofHom R.val.toRingHom)) ∧
        t ⁻¹ᵁ q.smoothLocus = ⊤ ∧
        Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t = (s ≫ E.inclusion).left ≫ f ∧
        Nonempty ((Scheme.Modules.pullback f).obj M ≅ E.smoothMarkingPower s m) := by
  obtain ⟨R, hR, hcR, Y, p, M, _, hp, hfp, hM, t, a, _, ht, ha, he, ⟨e⟩⟩ :=
    E.exists_smoothMarking_integer_model s m c₀ hc₀
  obtain ⟨U, hUc, hUs, hU⟩ := E.exists_smoothMarking_compact_neighborhood s
  obtain ⟨B, hB, hRB, Z, q, f, c, z, hq, hqfp, hz, hc, hf, hfc, hsm, hez⟩ :=
    exists_coefficient_smooth_marking_refinement R p ha (s ≫ E.inclusion).left
      (s ≫ E.inclusion).w t ht he U hUc hUs
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  let _ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian q
  let _ : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace q
  have hzclosed : IsClosedImmersion z := by
    have : IsClosedImmersion (z ≫ q) := by rw [hz]; infer_instance
    exact IsClosedImmersion.of_comp z q
  refine ⟨B, hB, fun x hx ↦ hRB (hcR hx), Z, q, (Scheme.Modules.pullback c).obj M,
    z, f, hq, hqfp, ⟨⟩, hM.pullback c, hzclosed, hz, hf, hsm, hez, ?_⟩
  exact ⟨(Scheme.Modules.pullbackComp f c).app M ≪≫
    (Scheme.Modules.pullbackCongr hfc).app M ≪≫ e⟩

end FLT.Mazur.GeneralizedEllipticCurve
