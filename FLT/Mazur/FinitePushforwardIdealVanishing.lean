/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePushforwardAmpleVanishing
public import FLT.Mazur.FinitePushforwardIdealImage

/-!
# Vanishing for ideal multiples of finite direct images

The actual ideal-image comparison transports Serre vanishing to every ideal
multiple of a finite direct image. These are the coefficient sheaves required
in the witness hypothesis of Stacks 01YM, used in finite-surjective descent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback GlobalIdealPower

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X Y : Scheme}
  (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (g : Y ⟶ X) [IsFinite g]

include f in
/-- An ample pullback kills the positive cohomology of all ideal-multiple twists. -/
theorem finitePushforward_ideal_ample_coherent_vanishing {L : X.Modules}
    (hL : LocallyFreeRankOne L) (hample : AmpleLineBundle ((pullback g).obj L))
    (M : Y.Modules) [M.IsFinitePresentation] (I : X.IdealSheafData) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH
        (tensor (multiple I ((pushforward g).obj M)) (tensorPower L n)) (q + 1)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨N, hN⟩ := finitePushforward_ample_coherent_vanishing f g hL hample
    (multiple (I.comap g) M)
  refine ⟨N, fun n hn q ↦ ?_⟩
  exact @moduleH_subsingleton_of_iso X _ _
    (ModuleSheafTensor.congr (FinitePushforwardIdealImage.iso g I M) (Iso.refl _))
    (q + 1) (hN n hn q)

end FLT.Mazur.FCurve
