/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCanonicalBasis
public import FLT.Mazur.PolygonCompletePointPoleProducts
public import FLT.Mazur.DivisorComplementCanonicalUnitor
public import FLT.Mazur.RelativePoleComplementFunctions

/-!
# Integral pole coordinates on the original Cartier complement

The canonical integral basis and normalized lifts give actual functions 1, x
and y. Original section products give their powers without smoothness or a group law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor relativePoleFunction

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

/-- The base scalars on the actual complement, through its original structure map. -/
def completePointComplementBaseMap :
    Γ(Spec (.of (PowerSeries K)), ⊤) →+*
      Γ(Scheme.Opens.toScheme (X := exactVeroneseProj K n h) (s).ker.support.compl, ⊤) :=
  (Scheme.Opens.ι (X := exactVeroneseProj K n h) (s).ker.support.compl).appTop.hom.comp
    (f).appTop.hom

/-- The order-two coordinate is the function of the original normalized lift. -/
def completePointComplementX :
    Γ(Scheme.Opens.toScheme (X := exactVeroneseProj K n h) (s).ker.support.compl, ⊤) :=
  relativePoleFunction f s hI 2
    (completePointPoleLift K n h i 0)

/-- The order-three coordinate is the function of the original normalized lift. -/
def completePointComplementY :
    Γ(Scheme.Opens.toScheme (X := exactVeroneseProj K n h) (s).ker.support.compl, ⊤) :=
  relativePoleFunction f s hI 3
    (completePointPoleLift K n h i 1)

/-- The canonical degree-one vector represents the constant one on the original complement. -/
theorem completePointComplement_oneBasis :
    relativePoleFunction f s hI 1 (completePointOneCanonicalBasis K n h i ()) = 1 := by
  unfold relativePoleFunction
  exact divisorComplementFunction_one_of_unitor hI _
    (completePointOneCanonicalBasis_section K n h i)

/-- The actual order-four product represents x squared. -/
theorem completePointComplement_square :
    relativePoleFunction f s hI 4 (completePointPoleSquare K n h i) =
      completePointComplementX K n h i ^ 2 := by
  exact (relativePoleFunction_product f s hI 2 2 _ _).trans
    (pow_two (completePointComplementX K n h i)).symm

/-- The actual order-five product represents xy. -/
theorem completePointComplement_mixed :
    relativePoleFunction f s hI 5 (completePointPoleMixed K n h i) =
      completePointComplementX K n h i * completePointComplementY K n h i := by
  exact relativePoleFunction_product f s hI 2 3 _ _

/-- The original order-six cube represents x cubed. -/
theorem completePointComplement_cube :
    relativePoleFunction f s hI 6 (completePointPoleCube K n h i) =
      completePointComplementX K n h i ^ 3 := by
  apply (relativePoleFunction_product f s hI 4 2 _ _).trans
  rw [completePointComplement_square]
  exact (pow_succ (completePointComplementX K n h i) 2).symm

/-- The original order-six square represents y squared. -/
theorem completePointComplement_ySquare :
    relativePoleFunction f s hI 6 (completePointPoleYSquare K n h i) =
      completePointComplementY K n h i ^ 2 := by
  exact (relativePoleFunction_product f s hI 3 3 _ _).trans
    (pow_two (completePointComplementY K n h i)).symm

end FLT.Mazur.PolygonInfinitesimalStages
