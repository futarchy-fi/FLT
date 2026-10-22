/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingPoleReduction
public import FLT.Mazur.RelativePoleComplementLinear
public import FLT.Mazur.RelativeGenusOneAllPoleBasis

/-!
# Compatible monomial bases in every positive relative pole degree

The actual unit-leading products extend the original constant vector at every
step. The finite indices retain their order, and old vectors use original inclusions.
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
local instance generalizedCurveMarkingAllPoleBasisProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- A basis in every original positive pole degree, built from actual monomial sections. -/
def smoothMarkingAllPoleBasis : (m : ℕ) → Module.Basis (Fin (m + 1)) Γ(S, ⊤)
    (ModuleRingH E.curve.hom.appTop.hom
      (tensorPower (divisorLineBundle (t).left.ker (hI)) (m + 1)) 0)
  | 0 => (smoothMarkingOneBasis E s).reindex (Equiv.ofUnique Unit (Fin 1))
  | m + 1 => (sectionPoleSpecifiedBasis E.curve.hom (t).left (t).w (hI) (m + 1)
      (sectionPoleMultiplicativeCoordinates (t).left (hI) e (m + 2))
      (smoothMarkingAllPoleBasis m) (smoothMarkingHigherMonomial E s e m)
      (smoothMarkingHigherMonomial_leading E s e m)).reindex
        (relativePoleIndexSucc (m + 1))

/-- The first basis retains the original canonical degree-one vector. -/
theorem smoothMarkingAllPoleBasis_zero (i : Fin 1) :
    smoothMarkingAllPoleBasis E s e 0 i = smoothMarkingOneBasis E s () := by
  rw [smoothMarkingAllPoleBasis, Module.Basis.reindex_apply]

/-- Each old vector enters the next degree by the original divisor step. -/
theorem smoothMarkingAllPoleBasis_old (m : ℕ) (i : Fin (m + 1)) :
    smoothMarkingAllPoleBasis E s e (m + 1) i.castSucc =
      divisorPowerRingStep E.curve.hom.appTop.hom (hI) (m + 1)
        (smoothMarkingAllPoleBasis E s e m i) := by
  rw [smoothMarkingAllPoleBasis, Module.Basis.reindex_apply, relativePoleIndexSucc_old]
  exact sectionPoleSpecifiedBasis_old _ _ _ _ _ _ _ _ _ i

/-- The last vector is the constructed actual monomial of that degree. -/
theorem smoothMarkingAllPoleBasis_last (m : ℕ) :
    smoothMarkingAllPoleBasis E s e (m + 1) (Fin.last (m + 1)) =
      smoothMarkingHigherMonomial E s e m := by
  rw [smoothMarkingAllPoleBasis, Module.Basis.reindex_apply, relativePoleIndexSucc_last]
  exact sectionPoleSpecifiedBasis_new _ _ _ _ _ _ _ _ _

end FLT.Mazur.GeneralizedEllipticCurve
