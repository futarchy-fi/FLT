/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClopenLimitDescent
public import FLT.Mazur.CoefficientModelFiniteness
public import FLT.Mazur.ProperCoverImmersionCriterion

/-!
# Closed open immersions descend to a coefficient stage

An open immersion into a finite-type model over a finite integer coefficient
ring becomes a closed immersion at some finite enlargement if it is closed
after extension to the original ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.Approximation

/-- The displayed base-change morphism has the expected inverse-image range. -/
lemma immersionBaseChange_range {Z P S T : Scheme.{u}}
    (q : Z ⟶ S) (p : P ⟶ S) (h : Z ⟶ P)
    (w : h ≫ p = q) (b : T ⟶ S) :
    Set.range (immersionBaseChange q p h w b) = pullback.fst p b ⁻¹' Set.range h := by
  have H := immersionBaseChange_isPullback q p h w b
  rw [← H.isoPullback_hom_fst]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr H.isoPullback.hom.surjective, Set.image_univ,
    Scheme.Pullback.range_fst]

/-- Closedness of an open immersion descends without a flatness hypothesis. -/
theorem exists_coefficient_closed_openImmersion {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Z P : Scheme.{u}} (p : P ⟶ Spec (.of S₀)) [QuasiCompact p] [LocallyOfFiniteType p]
    (h : Z ⟶ P) [IsOpenImmersion h]
    [IsClosedImmersion (immersionBaseChange (h ≫ p) p h rfl
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))] :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      IsClosedImmersion (immersionBaseChange (h ≫ p) p h rfl
        ((coefficientSpectrumToInitial S₀).app i)) := by
  let D := coefficientModelDiagram S₀ p
  let c := coefficientModelCone S₀ p
  let t : D ⟶ (Functor.const _).obj P :=
    { app i := pullback.fst p ((coefficientSpectrumToInitial S₀).app i)
      naturality _ _ _ := by simp [D, coefficientModelDiagram, schemeBaseChangeDiagram] }
  have hb (i) : c.π.app i ≫ t.app i =
      pullback.fst p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) := by
    simp [c, t, coefficientModelCone, schemeBaseChangeCone]
  have (i : (CoefficientStage S₀)ᵒᵖ) : IsNoetherian (D.obj i) := coefficientModel_isNoetherian p i
  have hclosed : IsClosed ((pullback.fst p
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) ⁻¹ᵁ h.opensRange : c.pt.Opens) :
        Set c.pt) := by
    change IsClosed ((pullback.fst p
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))) ⁻¹' Set.range h)
    exact (immersionBaseChange_range (h ≫ p) p h rfl
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))) ▸
      (immersionBaseChange (h ≫ p) p h rfl
        (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))).isClosedEmbedding.isClosed_range
  obtain ⟨i, hi⟩ := exists_isClosed_preimage_of_isLimit D c (coefficientModelIsLimit S₀ p)
    t _ hb h.opensRange hclosed
  refine ⟨i, ?_⟩
  have : IsOpenImmersion (immersionBaseChange (h ≫ p) p h rfl
      ((coefficientSpectrumToInitial S₀).app i)) :=
    MorphismProperty.of_isPullback (immersionBaseChange_isPullback _ _ _ _ _).flip
      inferInstance
  apply IsClosedImmersion.of_isPreimmersion
  rw [immersionBaseChange_range]
  exact hi

end FLT.Mazur.Approximation
