/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientProperDescent
public import FLT.Mazur.CoefficientModelRecovery
public import FLT.Mazur.FinitelyPresentedLineSheafDescent

/-!
# Proper finitely presented models with line-sheaf recovery

A proper finitely presented scheme over an arbitrary ring, together with
an invertible sheaf, descends to a proper finitely presented model over a
finite-type integer subalgebra. The recovery square is cartesian and the
model sheaf pulls back to the given sheaf along that very square.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- Proper finite-presentation descent retains both the cartesian recovery and
its invertible-sheaf identification, with any prescribed finite coefficients. -/
theorem exists_proper_finite_presentation_line_sheaf_descent {A : Type u} [CommRing A]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [IsProper p] [LocallyOfFinitePresentation p]
    (L : X.Modules) (hL : FLT.Mazur.FCurve.LocallyFreeRankOne L)
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of S)) (M : Y.Modules),
        IsProper q ∧ LocallyOfFinitePresentation q ∧
        FLT.Mazur.FCurve.LocallyFreeRankOne M ∧
        ∃ f : X ⟶ Y,
          IsPullback f p q (Spec.map (CommRingCat.ofHom (algebraMap S A))) ∧
          Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : X.IsSeparated := by
    constructor
    rw [← terminal.comp_from p]
    infer_instance
  obtain ⟨S₀, hS₀, hs₀, Y, q, M, hsep, hqc, hfp, hM, f, hf, ⟨e⟩⟩ :=
    exists_finite_presentation_separated_line_sheaf_descent p L hL s hs
  change IsPullback f p q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) at hf
  have hq : IsProper (pullback.snd q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))) := by
    rw [← hf.isoPullback_inv_snd]
    infer_instance
  obtain ⟨i, hi⟩ := exists_coefficient_isProper S₀ q hq
  refine ⟨i.unop.val, i.unop.property.2, fun x hx ↦ i.unop.property.1 (hs₀ hx),
    (coefficientModelDiagram S₀ q).obj i,
    pullback.snd q ((coefficientSpectrumToInitial S₀).app i),
    coefficientModelSheaf (q := q) i M, hi, inferInstance,
    coefficientModelSheaf_rankOne i hM, coefficientModelRecovery hf i,
    coefficientModelRecovery_isPullback hf i, ?_⟩
  exact ⟨coefficientModelSheafRecoveryIso hf i e⟩

end FLT.Mazur.Approximation
