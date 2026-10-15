/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DivisorLinePullbackTransport
public import FLT.Mazur.PolygonArithmeticBoundaryLine

/-!
# Coherence of the arithmetic boundary-line system

The canonical comparisons of actual divisor lines satisfy the identity and
composition laws, with all specified scheme-pullback transports retained.
These laws turn the constructed lines into a compatible formal polarization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- Identity arithmetic restriction gives the canonical pullback identity comparison. -/
theorem boundaryLineSystemIso_id (a : ℕ) :
    boundaryLineSystemIso A π n h (𝟙 a) =
      (pullbackCongr ((stageSystem A π n h).map_id a)).app (boundaryLine A π a n h) ≪≫
        (pullbackId ((family A π a n h).left)).app (boundaryLine A π a n h) := by
  let _ := boundaryIdeal_systemMap_isIso A π n h (𝟙 a)
  exact divisorLinePullbackIsoOfEq_id_eq _ ((stageSystem A π n h).map_id a)
    (boundaryIdeal A π a n h) (boundaryIdeal_cartier A π a n h).1
    (boundaryIdeal_systemMap A π n h (𝟙 a))

/-- The original arithmetic line comparisons obey the full pullback composition law. -/
theorem boundaryLineSystemIso_comp {a b c : ℕ} (f : a ⟶ b) (g : b ⟶ c) :
    (pullback ((stageSystem A π n h).map f)).mapIso (boundaryLineSystemIso A π n h g) ≪≫
        boundaryLineSystemIso A π n h f =
      (pullbackComp ((stageSystem A π n h).map f) ((stageSystem A π n h).map g)).app
          (boundaryLine A π c n h) ≪≫
        (pullbackCongr ((stageSystem A π n h).map_comp f g).symm).app
          (boundaryLine A π c n h) ≪≫ boundaryLineSystemIso A π n h (f ≫ g) := by
  let _ := boundaryIdeal_systemMap_isIso A π n h f
  let _ := boundaryIdeal_systemMap_isIso A π n h g
  let _ := boundaryIdeal_systemMap_isIso A π n h (f ≫ g)
  exact divisorLinePullbackIsoOfEq_comp_eq _ _ _ ((stageSystem A π n h).map_comp f g)
    (boundaryIdeal_cartier A π c n h).1 (boundaryIdeal_cartier A π b n h).1
    (boundaryIdeal_cartier A π a n h).1 (boundaryIdeal_systemMap A π n h g)
    (boundaryIdeal_systemMap A π n h f) (boundaryIdeal_systemMap A π n h (f ≫ g))

end FLT.Mazur.PolygonArithmeticStages
