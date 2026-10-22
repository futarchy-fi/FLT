/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCanonicalIntegerModel
public import FLT.Mazur.GeneralizedCurveMarkingBaseChange

/-!
# Canonical integer models on actual affine tests of an arbitrary base

Pull the original marked whole family to the specified affine test, then
construct its finite integer model. The model marking's own pole powers
recover the restrictions of the original pole powers, all on one model.
This applies in particular to every actual affine chart of the original base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Actual affine tests of any marked family admit canonical integer models of all pole powers. -/
theorem exists_smoothMarking_affine_canonical_model {S : Scheme}
    (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)
    {A : Type} [CommRing A] (g : Spec (.of A) ⟶ S) (c₀ : Set A) (hc₀ : c₀.Finite) :
    ∃ (R : Subalgebra ℤ A) (_ : Algebra.FiniteType ℤ R) (_ : c₀ ⊆ R)
      (Y : Scheme) (q : Y ⟶ Spec (.of R)) (t : Spec (.of R) ⟶ Y)
      (f : (E.baseChange g).curve.left ⟶ Y) (V : Y.Opens),
      IsProper q ∧ LocallyOfFinitePresentation q ∧ IsNoetherian Y ∧
        IsClosedImmersion t ∧ t ≫ q = 𝟙 _ ∧
        IsPullback f (E.baseChange g).curve.hom q
          (Spec.map (CommRingCat.ofHom R.val.toRingHom)) ∧
        t ⁻¹ᵁ V = ⊤ ∧ SmoothOfRelativeDimension 1 (V.ι ≫ q) ∧
        Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ t =
          (pullSection g s ≫ (E.baseChange g).inclusion).left ≫ f ∧
        ∃ hI : RelativeEffectiveCartier q t.ker, ∀ m : ℕ,
          Nonempty ((pullback f).obj (tensorPower (divisorLineBundle t.ker hI.1) m) ≅
            (pullback (Limits.pullback.fst E.curve.hom g)).obj (E.smoothMarkingPower s m)) := by
  obtain ⟨R, hR, hcR, Y, q, t, f, V, hp, hfp, hY, htc, ht, hf, hV, hd, he, hI, hM, _⟩ :=
    (E.baseChange g).exists_smoothMarking_canonical_integer_model (pullSection g s) c₀ hc₀
  refine ⟨R, hR, hcR, Y, q, t, f, V, hp, hfp, hY, htc, ht, hf, hV, hd, he,
    hI, fun m ↦ ?_⟩
  obtain ⟨e⟩ := hM m
  exact ⟨e ≪≫ (E.smoothMarkingPowerBaseChangeIso g s m).symm⟩

end FLT.Mazur.GeneralizedEllipticCurve
