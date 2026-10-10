/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InfinitesimalStructureProjection
public import FLT.Mazur.MaximalAdicDetection
public import FLT.Mazur.BaseAdicCohomologyImageStability

/-!
# Evaluation detects proper functions over a Noetherian base

Actual infinitesimal restrictions place an evaluation-zero function in every
cohomology image term. The proved cofinality of this filtration with the adic
filtration and finite proper cohomology force the original function to vanish.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.Chow.AffineBase
namespace FLT.Mazur.NoetherianProperEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : CommRingCat.{0}} [IsNoetherianRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec R) [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _)

include hs

/-- An evaluation-zero function on the original proper family is zero. -/
theorem eq_zero (x : Γ(X, ⊤)) (hx : s.appTop x = 0) : x = 0 := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let _ := Chow.source_isNoetherian f
  let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
  let _ := proper_coherent_hasFiniteRingCohomology f (structureModule X) 0
  let z : ModuleRingH (baseCohomologyScalars f) (structureModule X) 0 :=
    (moduleH0Equiv (structureModule X)).symm x
  have hz : z = 0 := by
    apply MaximalAdicDetection.eq_zero (R := R)
    intro J hJ n
    let _ := hJ
    obtain ⟨c, hc⟩ := BaseAdicCohomology.imageFiltration_cohomology_le_adic
      f J (structureModule X) 0
    apply hc n
    exact InfinitesimalStructureProjection.mem_cohomologyImage f s hs J (n + c) x hx
  have he := congrArg (moduleH0Equiv (structureModule X)) hz
  simpa only [z, LinearEquiv.apply_symm_apply, map_zero] using he

/-- The original section evaluation is injective, even for nonreduced Noetherian bases. -/
theorem injective : Function.Injective s.appTop := by
  intro x y h
  have hz := eq_zero f s hs (x - y) (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.mp hz

/-- Every global function is its scalar value pulled back from the original base. -/
theorem pullback_evaluation (x : Γ(X, ⊤)) : f.appTop (s.appTop x) = x := by
  apply injective f s hs
  exact SchemeRelativeNilpotentSections.evaluation_pullback f s hs (s.appTop x)

end FLT.Mazur.NoetherianProperEvaluation
