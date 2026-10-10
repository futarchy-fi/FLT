/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedLinePullback

/-!
# Homogeneous kernels of the original graded line pullback

Detect homogeneous kernel membership directly on the actual power map.
Keeping its pushforward target avoids expanding concrete scheme maps merely
to identify the inverse image of the top open.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SectionGradedLinePullback

open SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme} {L : Y.Modules} {M : X.Modules}

/-- Equality transport of the whole graded map retains the specified line comparison. -/
theorem ringHom_transport {f g : X ⟶ Y} (hf : f = g)
    (he : ((Scheme.Modules.pullback f).obj L ≅ M) =
      ((Scheme.Modules.pullback g).obj L ≅ M))
    (e : (Scheme.Modules.pullback f).obj L ≅ M) :
    ringHom f e = ringHom g (he.mp e) := by
  subst g
  rfl

/-- A homogeneous element vanishes under the ring map exactly when its power map vanishes. -/
theorem ringHom_of_eq_zero_iff (f : X ⟶ Y)
    (e : (Scheme.Modules.pullback f).obj L ≅ M) (d : ℕ) (s : Piece L ⊤ d) :
    ringHom f e (of L ⊤ d s) = 0 ↔ (powerMap f e d).app ⊤ s = 0 := by
  rw [ringHom_of]
  constructor
  · intro hs
    exact DirectSum.of_injective d (hs.trans (map_zero (of M ⊤ d)).symm)
  · intro hs
    change of M ⊤ d ((powerMap f e d).app ⊤ s) = 0
    rw [hs, map_zero]

end FLT.Mazur.SectionGradedLinePullback
