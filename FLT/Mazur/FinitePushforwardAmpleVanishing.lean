/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleCoherentVanishing
public import FLT.Mazur.AffinePushforwardCohomology

/-!
# Vanishing for finite direct images under an ample pullback

The line projection formula and affine cohomology comparison transport Serre
vanishing from the finite cover to its actual direct-image coefficients.
This is the direct-image step of Stacks 0B5V; extending it to all coherent
coefficients on the target requires a separate support dévissage argument.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X Y : Scheme}
  (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (g : Y ⟶ X) [IsFinite g]

include f in
/-- An ample pullback kills the high twists of every coherent finite direct image. -/
theorem finitePushforward_ample_coherent_vanishing {L : X.Modules}
    (hL : LocallyFreeRankOne L) (hample : AmpleLineBundle ((pullback g).obj L))
    (M : Y.Modules) [M.IsFinitePresentation] :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (tensor ((pushforward g).obj M) (tensorPower L n)) (q + 1)) := by
  have : X.IsSeparated := ⟨by rw [← CategoryTheory.Limits.terminal.comp_from f]; infer_instance⟩
  obtain ⟨N, hN⟩ := hample.coherent_vanishing (g ≫ f) M
  refine ⟨N, fun n hn q ↦ ?_⟩
  let P := tensor M ((pullback g).obj (tensorPower L n))
  have hP := tensor_line_isFinitePresentation M _ ((hL.tensorPower n).pullback g)
  have hzero : Subsingleton (ModuleH P (q + 1)) :=
    @moduleH_subsingleton_of_iso Y _ _
      (ModuleSheafTensor.congr (Iso.refl M) (tensorPowerIso g L n)) (q + 1) (hN n hn q)
  have hz := (affinePushforward_moduleH_subsingleton_iff g P (q + 1)).mpr hzero
  exact @moduleH_subsingleton_of_iso X _ _
    (ClosedLineProjectionFormula.projectionIso g M (tensorPower L n) (hL.tensorPower n)).symm
    (q + 1) hz

end FLT.Mazur.FCurve
