/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeContragredientEvaluation
public import FLT.Mazur.FiniteFreeDualProjectiveTransitions
public import FLT.Mazur.ProjectiveHomogeneousPointTransport

/-!
# Section points under the genuine dual projective transitions

The contragredient projective isomorphism transports an actual scheme point
by the original change of section coordinates. This identifies the coordinate
convention for the transitions used to glue the dual projective atlas.
-/

@[expose] public noncomputable section
open MvPolynomial AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FiniteFreeContragredient
open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {ι κ : Type u} [Finite ι] [Finite κ]

/-- Original section transport computes the actual dual projective scheme morphism. -/
lemma unitChartPoint_transport (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (v : ι →₀ R)
    (i : ι) (j : κ) (a b : Rˣ) (hi : v i = a) (hj : e v j = b) :
    unitChartPoint R ι (.id R) (fun k ↦ v k) i a hi ≫ (linearIso (map e)).hom =
      unitChartPoint R κ (.id R) (fun k ↦ e v k) j b hj := by
  apply unitChartPoint_linearIso_of_eval (map e) (.id R) _ _ _ i j a b hi hj
  apply RingHom.ext
  intro p
  exact evaluate_contragredient_apply e v p

/-- The dual projective chart preimage is cut out by the original coordinate functional. -/
lemma dual_preimage_chart (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (j : κ) :
    (linearIso (map e)).hom ⁻¹ᵁ chart R κ j =
      Proj.basicOpen (grading R ι)
        (linearForm ((map e).symm (Finsupp.single j 1))) :=
  linearIso_preimage_chart (map e) j

end FiniteFreeContragredient

namespace FiniteFreeChartTransitions
open AffineFreeSheafCoordinates ProjectiveSpace
open Scheme.Modules
variable {X : Scheme.{u}} (M : X.Modules)

/-- A genuine free-sheaf transition acts on section points by its recovered coordinates. -/
lemma dualProjectiveTransition_unitChartPoint {U V W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ)
    (v : ι →₀ Γ(W.toScheme, ⊤)) (i : ι) (j : κ) (a b : Γ(W.toScheme, ⊤)ˣ)
    (hi : v i = a) (hj : coordinates W.toScheme (transition M hU hV e d) v j = b) :
    unitChartPoint Γ(W.toScheme, ⊤) ι (.id _) (fun k ↦ v k) i a hi ≫
        (dualProjectiveTransition M hU hV e d).hom =
      unitChartPoint Γ(W.toScheme, ⊤) κ (.id _)
        (fun k ↦ coordinates W.toScheme (transition M hU hV e d) v k) j b hj :=
  FiniteFreeContragredient.unitChartPoint_transport _ v i j a b hi hj

end FiniteFreeChartTransitions
end FLT.Mazur
