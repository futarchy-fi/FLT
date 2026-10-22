/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientSmoothDescent
public import FLT.Mazur.CoefficientModelRecovery

/-!
# Smoothness of a fixed model open after finite enlargement

If an open of the fixed model is smooth after recovery, its literal inverse
image is smooth at a finite coefficient enlargement. The whole family is
kept and is not assumed smooth or flat.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A model open smooth on the original family becomes smooth at finite coefficients. -/
theorem exists_coefficient_smooth_open {A : Type u} [CommRing A]
    (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
    {X Y : Scheme.{u}} {r : X ⟶ Spec (.of A)} (p : Y ⟶ Spec (.of R))
    [QuasiCompact p] [LocallyOfFinitePresentation p] {a : X ⟶ Y}
    (h : IsPullback a r p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    (V : Y.Opens) [Smooth ((a ⁻¹ᵁ V).ι ≫ r)] :
    ∃ i : (CoefficientStage R)ᵒᵖ,
      Smooth ((pullback.fst p ((coefficientSpectrumToInitial R).app i) ⁻¹ᵁ V).ι ≫
        pullback.snd p ((coefficientSpectrumToInitial R).app i)) := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let _ : IsNoetherian Y := ⟨⟩
  let _ : QuasiCompact V.ι := inferInstance
  have hV := (isPullback_morphismRestrict a V).paste_vert h
  obtain ⟨i, _, hi⟩ := exists_coefficient_smooth_of_cartesian R
    ((a ⁻¹ᵁ V).ι ≫ r) (V.ι ≫ p) hV ∅ Set.finite_empty
  let bi := (coefficientSpectrumToInitial R).app i
  have hVi := (isPullback_morphismRestrict (pullback.fst p bi) V).paste_vert
    (IsPullback.of_hasPullback p bi)
  refine ⟨i, ?_⟩
  rw [← hVi.isoPullback_hom_snd]
  infer_instance

end FLT.Mazur.Approximation
