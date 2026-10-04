/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedCoordinateEvaluation

/-!
# Independence of line coordinates for homogeneous fractions

For numerator and denominator of the same tensor degree, evaluation is the
unique scalar taking denominator to numerator. Thus the degree-zero
localization map is independent of the line trivialization used to define it.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedCoordinateEvaluation
open FCurve SectionGradedMultiplication SectionGradedSum SectionGradedCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} {L : X.Modules} (e : L ≅ structureModule X) (U : X.Opens)

/-- A coordinate ratio is characterized by the actual scalar equation on sections. -/
lemma coordinate_equation_iff (n : ℕ) (r : Γ(X, U)) (s t : Piece L U n) :
    r * coordinate e n U s = coordinate e n U t ↔ r • s = t := by
  constructor
  · intro h
    apply coordinate_injective e n U
    change (tensorPowerTrivialization e n).hom.app U (r • s) = _
    rw [Hom.app_smul]
    exact h
  · rintro rfl
    exact (Hom.app_smul
      (tensorPowerTrivialization e n).hom r s).symm

variable [Fact (LocallyFreeRankOne L)]

/-- Chart evaluation satisfies the intrinsic scalar equation in every tensor degree. -/
lemma awayEval_mk_equation (f : SectionGradedSum.Sections L U)
    (hf : IsUnit (ringEval e U f))
    (c : HomogeneousLocalization.NumDenSameDeg (grade L U) (Submonoid.powers f))
    (s t : Piece L U c.deg) (hs : of L U c.deg s = c.den)
    (ht : of L U c.deg t = c.num) :
    awayEval e U f hf (HomogeneousLocalization.mk c) • s = t := by
  apply (coordinate_equation_iff e U c.deg _ s t).mp
  rw [← ringEval_of, ← ringEval_of, hs, ht]
  exact awayEval_mk_mul e U f hf c

/-- Powers of a unit-coordinate denominator still have unit coordinates. -/
lemma ringEval_den_isUnit (f : SectionGradedSum.Sections L U)
    (hf : IsUnit (ringEval e U f))
    (c : HomogeneousLocalization.NumDenSameDeg (grade L U) (Submonoid.powers f)) :
    IsUnit (ringEval e U c.den) := by
  obtain ⟨n, hn⟩ := c.den_mem
  rw [← hn, map_pow]
  exact hf.pow n

/-- Homogeneous localization evaluation is independent of the chosen line coordinates. -/
lemma awayEval_independent (e' : L ≅ structureModule X)
    (f : SectionGradedSum.Sections L U)
    (hf : IsUnit (ringEval e U f)) (hf' : IsUnit (ringEval e' U f)) :
    awayEval e U f hf = awayEval e' U f hf' := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨s, hs⟩ := c.den.property
  obtain ⟨t, ht⟩ := c.num.property
  apply (ringEval_den_isUnit e' U f hf' c).mul_left_inj.mp
  rw [awayEval_mk_mul e' U f hf' c]
  rw [← hs, ← ht, ringEval_of, ringEval_of]
  exact (coordinate_equation_iff e' U c.deg _ s t).mpr
    (awayEval_mk_equation e U f hf c s t hs ht)

end FLT.Mazur.SectionGradedCoordinateEvaluation
