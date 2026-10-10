/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InfinitesimalClosedFiberFunctions
public import FLT.Mazur.NoetherianProperEvaluation

/-!
# Local proper functions determined by the closed fiber

Over a Noetherian local ring, connectedness of the single reduced closed fiber
suffices to determine all global functions on a pointed flat proper family
with geometrically reduced fibers. Completeness of the base is not required.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.Chow.AffineBase
namespace FLT.Mazur.NoetherianLocalClosedFiberFunctions
open Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : CommRingCat.{0}} [IsNoetherianRing R] [IsLocalRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec R) [IsProper f] [Flat f] [GeometricallyReduced f]
  (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _)
  (hc : (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) ∈
    geometricallyConnectedLocus f)

include hs hc

/-- Evaluation detects every global function using only the local base's closed fiber. -/
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
    have hcJ : (⟨J, inferInstance⟩ : PrimeSpectrum R) ∈ geometricallyConnectedLocus f := by
      simpa only [IsLocalRing.eq_maximalIdeal hJ] using hc
    obtain ⟨c, h⟩ := BaseAdicCohomology.imageFiltration_cohomology_le_adic
      f J (structureModule X) 0
    apply h n
    exact InfinitesimalClosedFiberFunctions.mem_cohomologyImage f s hs J hcJ (n + c) x hx
  have he := congrArg (moduleH0Equiv (structureModule X)) hz
  simpa only [z, LinearEquiv.apply_symm_apply, map_zero] using he

/-- Evaluation on the section is injective over the original local base. -/
theorem evaluation_injective : Function.Injective s.appTop := by
  intro x y h
  exact sub_eq_zero.mp (eq_zero f s hs hc (x - y) (by rw [map_sub, h, sub_self]))

/-- The actual structural pullback is bijective without any completeness hypothesis. -/
theorem appTop_bijective : Function.Bijective f.appTop := by
  refine ⟨Function.LeftInverse.injective
    (SchemeRelativeNilpotentSections.evaluation_pullback f s hs), fun x ↦ ?_⟩
  refine ⟨s.appTop x, evaluation_injective f s hs hc ?_⟩
  exact SchemeRelativeNilpotentSections.evaluation_pullback f s hs (s.appTop x)

omit hc in
/-- Ordinary connectedness of the actual closed fiber suffices for the local comparison. -/
theorem appTop_bijective_of_connected_closedFiber
    [ConnectedSpace (f.fiber ⟨IsLocalRing.maximalIdeal R, inferInstance⟩)] :
    Function.Bijective f.appTop := by
  let b : Spec R := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  let _ : IsReduced (f.fiber b) :=
    GeometricallyReduced.geometrically_isReduced (f := f)
      ((Spec R).fromSpecResidueField b) _ _ (.of_hasPullback _ _)
  exact appTop_bijective f s hs (mem_locus_of_connected_reduced_fiber f s hs b)

end FLT.Mazur.NoetherianLocalClosedFiberFunctions
