/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingHigherMonomials
public import FLT.Mazur.SectionPoleSpecifiedBasis

/-!
# Reduction of every original section by a unit-leading monomial

Exactness of the original pole sequence removes the actual leading coefficient
using the constructed higher monomial. The remainder has the preceding pole bound.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle
  sectionPoleMultiplicativeCoordinates Scheme.Modules.pullback
  relativePoleFunction

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

/-- The structure morphism is proper for the original family. -/
local instance generalizedCurveMarkingPoleReductionProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The common-frame leading coordinate of the new monomial is exactly one. -/
theorem smoothMarkingHigherMonomial_leading (m : ℕ) :
    sectionPoleLeadingCoordinate E.curve.hom (t).left (t).w (hI) (m + 1)
      (sectionPoleMultiplicativeCoordinates (t).left (hI) e (m + 2))
      (smoothMarkingHigherMonomial E s e m) = 1 :=
  (sectionPoleCoefficient_leading (t).left (hI) e E.curve.hom (t).w (m + 1) _).symm.trans
    (smoothMarkingHigherMonomial_coefficient E s e m)

/-- Subtracting the actual leading monomial leaves an original lower-pole section. -/
theorem smoothMarkingHigherMonomial_decomposition (m : ℕ)
    (z : ModuleRingH E.curve.hom.appTop.hom
      (tensorPower (divisorLineBundle (t).left.ker (hI)) (m + 2)) 0) :
    ∃ w : ModuleRingH E.curve.hom.appTop.hom
        (tensorPower (divisorLineBundle (t).left.ker (hI)) (m + 1)) 0,
      ∃ a : Γ(S, ⊤), z = divisorPowerRingStep E.curve.hom.appTop.hom (hI) (m + 1) w +
        a • smoothMarkingHigherMonomial E s e m := by
  let g := sectionPoleLeadingCoordinate E.curve.hom (t).left (t).w (hI) (m + 1)
    (sectionPoleMultiplicativeCoordinates (t).left (hI) e (m + 2))
  let v := smoothMarkingHigherMonomial E s e m
  have hv : g v = 1 := smoothMarkingHigherMonomial_leading E s e m
  have hz : g (z - g z • v) = 0 := by
    rw [map_sub, g.map_smul, hv, smul_eq_mul, mul_one, sub_self]
  obtain ⟨w, hw⟩ := (sectionPoleLeadingCoordinate_exact E.curve.hom (t).left (t).w (hI) (m + 1)
    (sectionPoleMultiplicativeCoordinates (t).left (hI) e (m + 2)) (z - g z • v)).mp hz
  exact ⟨w, g z, (congrArg (fun u ↦ u + g z • v) hw).trans
    (sub_add_cancel z (g z • v)) |>.symm⟩

end FLT.Mazur.GeneralizedEllipticCurve
