/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientIndependentLineDescent
public import FLT.Mazur.GeometricAcyclicRankOne

/-!
# Independent line models over arbitrary ring tests of a finite-type base

Factor the test ring map through its image, then descend only the line
through coefficient enlargements. No injectivity or finite-type condition
is imposed on the test map or the test ring.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.Approximation
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type} [CommRing R] [CommRing A] [Algebra.FiniteType ℤ R]
  {X Y : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ Spec (.of A)} {q : Y ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q]
  (g : R →+* A) (h : IsPullback a f q (Spec.map (CommRingCat.ofHom g)))

include h in
/-- Every line on any ring test has a Noetherian model retaining the actual family geometry. -/
theorem finiteTypeBase_independent_line_model (L : X.Modules) (hL : LocallyFreeRankOne L) :
    ∃ (Z B : Scheme.{0}) (r : Z ⟶ B) (p : X ⟶ Z) (b : Spec (.of A) ⟶ B) (M : Z.Modules),
      IsLocallyNoetherian B ∧ IsProper r ∧ Flat r ∧ GeometricallyIntegral r ∧
        LocallyFreeRankOne M ∧ IsPullback p f r b ∧
          Nonempty ((Scheme.Modules.pullback p).obj M ≅ L) := by
  let R₀ := g.toIntAlgHom.range
  let _ : Algebra.FiniteType ℤ R₀ := Algebra.FiniteType.of_surjective
    g.toIntAlgHom.rangeRestrict g.toIntAlgHom.rangeRestrict_surjective
  let k := Spec.map (CommRingCat.ofHom g.toIntAlgHom.rangeRestrict.toRingHom)
  let b := Spec.map (CommRingCat.ofHom R₀.val.toRingHom)
  have hb : b ≫ k = Spec.map (CommRingCat.ofHom g) := by
    rw [← Spec.map_comp]
    rfl
  let q₀ := pullback.snd q k
  let a₀ := pullback.lift a (f ≫ b) (by rw [Category.assoc, hb]; exact h.w)
  have H : IsPullback a₀ f q₀ b := by
    apply IsPullback.of_right _ (by simp [a₀]) (IsPullback.of_hasPullback q k)
    simpa only [a₀, pullback.lift_fst, hb] using h
  obtain ⟨i, M, hM, he⟩ := exists_coefficient_independent_line_cartesian R₀ q₀ H L hL
  let _ : Algebra.FiniteType ℤ i.unop.val := i.unop.property.2
  let _ : IsNoetherianRing i.unop.val := Algebra.FiniteType.isNoetherianRing ℤ i.unop.val
  refine ⟨(coefficientModelDiagram R₀ q₀).obj i, Spec (.of i.unop.val),
    pullback.snd q₀ ((coefficientSpectrumToInitial R₀).app i), coefficientModelRecovery H i,
    (coefficientSpectrumCone R₀).π.app i, M, inferInstance, inferInstance, inferInstance,
    inferInstance, hM, coefficientModelRecovery_isPullback H i, he⟩

end FLT.Mazur.Approximation
