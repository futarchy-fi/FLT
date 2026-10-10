/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientSmoothConnectedDescent
public import FLT.Mazur.ProperSmoothPointedLineSheafDescent

/-!
# Connected proper smooth models retaining the section and line sheaf

The actual connected-fiber open locus yields a finite coefficient model with
all the geometric properties, section recovery, and invertible-sheaf recovery.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation

/-- Connected proper smooth pointed line-sheaf data descend together to finite coefficients. -/
theorem exists_connected_proper_smooth_pointed_line_sheaf_descent {A : Type} [CommRing A]
    {X : Scheme.{0}} (p : X ⟶ Spec (.of A)) [IsProper p] [Smooth p]
    [GeometricallyConnected p] (s : Spec (.of A) ⟶ X) (hs : s ≫ p = 𝟙 _)
    (L : X.Modules) (hL : FCurve.LocallyFreeRankOne L) (c : Set A) (hc : c.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ c ⊆ S ∧
      ∃ (Y : Scheme.{0}) (q : Y ⟶ Spec (.of S)) (M : Y.Modules),
        IsProper q ∧ Smooth q ∧ GeometricallyConnected q ∧ FCurve.LocallyFreeRankOne M ∧
        ∃ (t : Spec (.of S) ⟶ Y) (f : X ⟶ Y),
          t ≫ q = 𝟙 _ ∧
          IsPullback f p q (Spec.map (CommRingCat.ofHom S.val.toRingHom)) ∧
          Spec.map (CommRingCat.ofHom S.val.toRingHom) ≫ t = s ≫ f ∧
          Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by
  obtain ⟨S₀, hS₀, hc₀, Y, q, M, hq, hsm, hM, t, f, ht, hf, _, ⟨e⟩⟩ :=
    exists_proper_smooth_pointed_line_sheaf_descent p s hs L hL c hc
  obtain ⟨i, hi⟩ := exists_coefficient_geometricallyConnected_of_proper_smooth S₀ hf t ht
  let qi := pullback.snd q ((coefficientSpectrumToInitial S₀).app i)
  let Mi := coefficientModelSheaf (q := q) i M
  have hMi : FCurve.LocallyFreeRankOne Mi := coefficientModelSheaf_rankOne i hM
  have hfi := coefficientModelRecovery_isPullback hf i
  let ei := coefficientModelSheafRecoveryIso hf i e
  obtain ⟨j, tj, htj, hej⟩ := exists_coefficient_section hfi s hs
  refine ⟨j.unop.val, j.unop.property.2,
    fun x hx ↦ j.unop.property.1 (i.unop.property.1 (hc₀ hx)),
    (coefficientModelDiagram i.unop.val qi).obj j,
    pullback.snd qi ((coefficientSpectrumToInitial i.unop.val).app j),
    coefficientModelSheaf (q := qi) j Mi, inferInstance, inferInstance, inferInstance,
    coefficientModelSheaf_rankOne j hMi, tj, coefficientModelRecovery hfi j,
    htj, coefficientModelRecovery_isPullback hfi j, hej, ?_⟩
  exact ⟨coefficientModelSheafRecoveryIso hfi j ei⟩

end FLT.Mazur.Approximation
