/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointPoleFrame
public import FLT.Mazur.SectionPoleHZeroMultiplication

/-!
# Products of normalized integral pole lifts

The common point-line frame normalizes the actual square, mixed product,
cube and order-three square over the original complete base. These are
products of original global sections, without a group law assumption.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor sectionPoleMultiplicativeCoordinates

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Leading coefficient of an actual complete-base H0 pole section in the common frame. -/
def completePointPoleCoefficient (i : Fin n) (m : ℕ)
    (x : ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) m) 0) :
    Γ(Spec (.of (PowerSeries K)), ⊤) :=
  sectionPoleCoefficient (completeBaseMarking K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 (completePointSectionFrame K n h i) m
    (moduleH0Equiv _ x)

/-- Every normalized lift has coefficient one in powers of the single original frame. -/
theorem completePointPoleLift_coefficient (i : Fin n) (m : ℕ) :
    completePointPoleCoefficient K n h i (m + 2) (completePointPoleLift K n h i m) = 1 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact (sectionPoleCoefficient_leading (completeBaseMarking K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 (completePointSectionFrame K n h i)
    (exactVeroneseProjToBase K n h) (completeBaseMarking_toBase K n h i) (m + 1) _).trans
      (completePointPoleLift_leading K n h i m)

/-- The original H0 product of complete-base point powers. -/
def completePointPoleProduct (i : Fin n) (a b : ℕ)
    (x : ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) a) 0)
    (y : ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) b) 0) :
    ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) (a + b)) 0 :=
  sectionPoleHZeroProduct (exactVeroneseProjToBase K n h) (completeBaseMarking K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 a b x y

/-- Actual section products multiply their common-frame leading coefficients. -/
theorem completePointPoleProduct_coefficient (i : Fin n) (a b : ℕ)
    (x : ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) a) 0)
    (y : ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) b) 0) :
    completePointPoleCoefficient K n h i (a + b) (completePointPoleProduct K n h i a b x y) =
      completePointPoleCoefficient K n h i a x * completePointPoleCoefficient K n h i b y :=
  sectionPoleHZeroProduct_coefficient (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_relativeCartier K n h i).1
    (completePointSectionFrame K n h i) a b x y

/-- Square of the original integral order-two lift. -/
def completePointPoleSquare (i : Fin n) :=
  completePointPoleProduct K n h i 2 2
    (completePointPoleLift K n h i 0) (completePointPoleLift K n h i 0)

/-- Mixed product of the original order-two and order-three lifts. -/
def completePointPoleMixed (i : Fin n) :=
  completePointPoleProduct K n h i 2 3
    (completePointPoleLift K n h i 0) (completePointPoleLift K n h i 1)

/-- Cube formed by multiplying the actual square by the original order-two lift. -/
def completePointPoleCube (i : Fin n) :=
  completePointPoleProduct K n h i 4 2
    (completePointPoleSquare K n h i) (completePointPoleLift K n h i 0)

/-- Square of the original integral order-three lift. -/
def completePointPoleYSquare (i : Fin n) :=
  completePointPoleProduct K n h i 3 3
    (completePointPoleLift K n h i 1) (completePointPoleLift K n h i 1)

/-- The square has unit leading coefficient in degree four. -/
theorem completePointPoleSquare_coefficient (i : Fin n) :
    completePointPoleCoefficient K n h i 4 (completePointPoleSquare K n h i) = 1 := by
  rw [completePointPoleSquare, completePointPoleProduct_coefficient K n h i 2 2,
    completePointPoleLift_coefficient K n h i 0, one_mul]

/-- The mixed product has unit leading coefficient in degree five. -/
theorem completePointPoleMixed_coefficient (i : Fin n) :
    completePointPoleCoefficient K n h i 5 (completePointPoleMixed K n h i) = 1 := by
  rw [completePointPoleMixed, completePointPoleProduct_coefficient K n h i 2 3,
    completePointPoleLift_coefficient K n h i 0, completePointPoleLift_coefficient K n h i 1,
    one_mul]

/-- The cube has unit leading coefficient in degree six. -/
theorem completePointPoleCube_coefficient (i : Fin n) :
    completePointPoleCoefficient K n h i 6 (completePointPoleCube K n h i) = 1 := by
  rw [completePointPoleCube, completePointPoleProduct_coefficient K n h i 4 2,
    completePointPoleSquare_coefficient, completePointPoleLift_coefficient K n h i 0, one_mul]

/-- The order-three square has the same leading coefficient as the order-two cube. -/
theorem completePointPoleYSquare_coefficient (i : Fin n) :
    completePointPoleCoefficient K n h i 6 (completePointPoleYSquare K n h i) = 1 := by
  rw [completePointPoleYSquare, completePointPoleProduct_coefficient K n h i 3 3,
    completePointPoleLift_coefficient K n h i 1, one_mul]

end FLT.Mazur.PolygonInfinitesimalStages
