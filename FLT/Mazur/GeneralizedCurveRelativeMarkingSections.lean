/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurvePointFiberCohomology
public import FLT.Mazur.ProperLinePushforwardLocalFree
public import FLT.Mazur.ProperLinePushforwardBaseChange

/-!
# Relative pole sections across singular generalized-curve fibers

The actual positive pole line is acyclic over a noetherian affine base.
Its section module is finite projective, and the canonical direct-image
comparison is an isomorphism for arbitrary affine base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve LineSectionBaseChange Chow
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group) (m : ℕ) (hm : 0 < m)

include hm

omit [IsNoetherianRing Γ(S, ⊤)] in
/-- The residue-algebra fibers of the original pole coefficient are acyclic. -/
theorem smoothMarkingPower_residue_acyclic (z : PrimeSpectrum Γ(S, ⊤)) (r : ℕ) :
    Subsingleton (ModuleH (residueAlgebraFiberLine E.curve.hom
      (E.smoothMarkingPower s m) z) (r + 1)) :=
  E.smoothMarkingPower_fieldFiber_acyclic s m hm
    (AffineBaseChangeCoefficients.baseMap S z.asIdeal.ResidueField) r

/-- Positive pole powers are acyclic on the original singular family over its affine base. -/
theorem smoothMarkingPower_relative_acyclic (r : ℕ) :
    Subsingleton (ModuleH (E.smoothMarkingPower s m) (r + 1)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Flat E.curve.hom := E.family.family.2.1
  exact positive_vanishing_of_residue_fibers E.curve.hom _
    (E.smoothMarkingPower_rankOne s m) (E.smoothMarkingPower_residue_acyclic s m hm) r

/-- The actual relative pole module is finite projective, including across singular fibers. -/
theorem smoothMarkingPower_sections_finite_projective :
    Module.Finite Γ(S, ⊤) (baseSections (E.smoothMarkingPower s m) E.curve.hom.appTop.hom ⊤) ∧
    Module.Projective Γ(S, ⊤)
      (baseSections (E.smoothMarkingPower s m) E.curve.hom.appTop.hom ⊤) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Flat E.curve.hom := E.family.family.2.1
  let hL := E.smoothMarkingPower_rankOne s m
  let _ := hL.isFinitePresentation
  exact ⟨proper_sections_finite E.curve.hom _,
    projective_sections_of_residue_fibers E.curve.hom _ hL
      (E.smoothMarkingPower_residue_acyclic s m hm)⟩

/-- The original positive pole direct image is locally finite free. -/
theorem smoothMarkingPower_pushforward_locallyFiniteFree :
    LocallyFiniteFree ((pushforward E.curve.hom).obj (E.smoothMarkingPower s m)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Flat E.curve.hom := E.family.family.2.1
  exact properLinePushforward_locallyFiniteFree E.curve.hom _
    (E.smoothMarkingPower_rankOne s m) (E.smoothMarkingPower_residue_acyclic s m hm)

/-- Canonical base change of the original pole direct image, with no flatness required of g. -/
def smoothMarkingPowerPushforwardIso {P T : Scheme} [IsAffine T]
    {p : P ⟶ E.curve.left} {q : P ⟶ T} {g : T ⟶ S}
    (h : IsPullback p q E.curve.hom g) :
    (pullback g).obj ((pushforward E.curve.hom).obj (E.smoothMarkingPower s m)) ≅
      (pushforward q).obj ((pullback p).obj (E.smoothMarkingPower s m)) := by
  letI : IsProper E.curve.hom := E.family.family.1
  letI : Flat E.curve.hom := E.family.family.2.1
  exact properLinePushforwardBaseChangeIso h _ (E.smoothMarkingPower_rankOne s m)
    (E.smoothMarkingPower_residue_acyclic s m hm)

end FLT.Mazur.GeneralizedEllipticCurve
