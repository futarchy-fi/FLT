/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientCartesianHomDescent
public import FLT.Mazur.CoefficientModelRecovery

/-!
# Descending maps while retaining the original families

The map to be descended is a map between the original schemes, with their
specified Cartesian models. The resulting finite-stage map retains those
same recovery maps, rather than replacing the original family by a pullback.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Model recovery followed by the canonical pullback comparison is the original recovery. -/
theorem coefficientModelRecovery_comparison {A : Type u} [CommRing A]
    {R : Subalgebra ℤ A} {X Y : Scheme.{u}} {a : X ⟶ Y}
    {r : X ⟶ Spec (.of A)} {p : Y ⟶ Spec (.of R)}
    (h : IsPullback a r p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (i : (CoefficientStage R)ᵒᵖ) :
    h.isoPullback.hom ≫ (coefficientModelCone R p).π.app i =
      coefficientModelRecovery h i := by
  apply pullback.hom_ext
  · simp [coefficientModelCone, schemeBaseChangeCone, coefficientModelRecovery,
      pullback.map, Category.assoc]
  · simp only [Category.assoc, coefficientModelCone, schemeBaseChangeCone,
      pullback.map, pullback.lift_snd, coefficientModelRecovery]
    rw [← Category.assoc, h.isoPullback_hom_snd]

/-- A map of original families descends with its specified Cartesian recovery maps. -/
theorem exists_coefficient_original_hom {A : Type u} [CommRing A]
    (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
    {X X' Y Z : Scheme.{u}} {r : X ⟶ Spec (.of A)} {r' : X' ⟶ Spec (.of A)}
    (p : Y ⟶ Spec (.of R)) (q : Z ⟶ Spec (.of R))
    [QuasiCompact p] [LocallyOfFiniteType p] [LocallyOfFinitePresentation q]
    {a : X ⟶ Y} {b : X' ⟶ Z}
    (hp : IsPullback a r p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (hq : IsPullback b r' q (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (F : X ⟶ X') (hF : F ≫ r' = r) :
    ∃ (i : (CoefficientStage R)ᵒᵖ)
      (f : (coefficientModelDiagram R p).obj i ⟶ (coefficientModelDiagram R q).obj i),
      f ≫ pullback.snd q ((coefficientSpectrumToInitial R).app i) =
        pullback.snd p ((coefficientSpectrumToInitial R).app i) ∧
      F ≫ coefficientModelRecovery hq i = coefficientModelRecovery hp i ≫ f := by
  let G := hp.isoPullback.inv ≫ F ≫ hq.isoPullback.hom
  have hG : G ≫ pullback.snd q (Spec.map (CommRingCat.ofHom R.val.toRingHom)) =
      pullback.snd p (Spec.map (CommRingCat.ofHom R.val.toRingHom)) := by
    simp only [G, Category.assoc, hq.isoPullback_hom_snd, hF, hp.isoPullback_inv_snd]
  obtain ⟨i, f, hf, hcart⟩ := exists_coefficient_cartesian_hom R p q G hG
  refine ⟨i, f, hf, ?_⟩
  rw [← coefficientModelRecovery_comparison hp i,
    ← coefficientModelRecovery_comparison hq i, ← Category.assoc]
  have he := congrArg (fun k ↦ hp.isoPullback.hom ≫ k) hcart.w
  simpa only [G, Category.assoc, Iso.hom_inv_id_assoc] using he

end FLT.Mazur.Approximation
