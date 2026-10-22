/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingAllPoleBasis

/-!
# Independence of all original relative monomial functions

Every finite initial segment is the faithful image of an actual original pole
basis. This proves independence over the base ring without a field hypothesis.
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
local instance generalizedCurveMarkingMonomialIndependenceProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The ordered sequence of original constant and higher monomial functions. -/
def smoothMarkingOrderedFunction : ℕ → relativePoleComplementModule E.curve.hom (t).left
  | 0 => relativePoleFunction E.curve.hom (t).left (hI) 1 (smoothMarkingOneBasis E s ())
  | m + 1 => relativePoleFunction E.curve.hom (t).left (hI) (m + 2)
      (smoothMarkingHigherMonomial E s e m)

/-- The original basis at each pole bound retains the same ordered function sequence. -/
theorem smoothMarkingAllPoleBasis_function (m : ℕ) (i : Fin (m + 1)) :
    relativePoleFunction E.curve.hom (t).left (hI) (m + 1)
      (smoothMarkingAllPoleBasis E s e m i) =
        smoothMarkingOrderedFunction E s e i := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rw [smoothMarkingAllPoleBasis_zero]
    rfl
  | succ m ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [smoothMarkingAllPoleBasis_last]
      rfl
    · rw [smoothMarkingAllPoleBasis_old, relativePoleFunction_step]
      exact ih j

/-- Every positive initial segment is independent over the actual base section ring. -/
theorem smoothMarkingOrderedFunction_initialIndependent (m : ℕ) :
    LinearIndependent Γ(S, ⊤)
      (fun i : Fin (m + 1) ↦ smoothMarkingOrderedFunction E s e i) := by
  have h := (smoothMarkingAllPoleBasis E s e m).linearIndependent.map'
    (relativePoleFunctionLinear E.curve.hom (t).left (hI) (m + 1))
    (LinearMap.ker_eq_bot.mpr (relativePoleFunction_injective E.curve.hom (t).left (hI) (m + 1)))
  change LinearIndependent Γ(S, ⊤) (fun i ↦
    (show relativePoleComplementModule E.curve.hom (t).left from
      relativePoleFunction E.curve.hom (t).left (hI) (m + 1)
        (smoothMarkingAllPoleBasis E s e m i))) at h
  simpa only [smoothMarkingAllPoleBasis_function] using h

/-- The entire original monomial sequence is independent over the base ring. -/
theorem smoothMarkingOrderedFunction_independent :
    LinearIndependent Γ(S, ⊤) (smoothMarkingOrderedFunction E s e) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro indices
  let j : indices → Fin (indices.sup id + 1) := fun i ↦
    ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  exact (smoothMarkingOrderedFunction_initialIndependent E s e (indices.sup id)).comp j
    (fun i k hik ↦ Subtype.ext (congrArg Fin.val hik))

end FLT.Mazur.GeneralizedEllipticCurve
