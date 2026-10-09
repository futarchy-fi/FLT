/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RationalCyclicCartierGenerator
public import FLT.Mazur.AmpleCyclicClassPresheaf
public import FLT.Mazur.GeneralizedCurveFiberAmple

/-!
# The ample cyclic moduli class of a rational torsion point

On a smooth geometrically integral generalized elliptic curve, the constructed
finite subgroup divisor has nonempty support and is ample by the proved curve
criterion. Together with its actual Cartier generator this constructs a point
of the ample cyclic moduli presheaf over the original field.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.GeneralizedEllipticCurve

open FiniteSubgroup

variable {K : Type} [Field K] (E : GeneralizedEllipticCurve (Spec (.of K)))
  {n : ℕ} [NeZero n] (P : 𝟙_ (Over (Spec (.of K))) ⟶ E.group) (ho : orderOf P = n)

/-- The rational subgroup has nonempty actual divisor support. -/
theorem rationalCyclicSubgroup_support_nonempty :
    ((E.rationalCyclicSubgroup P ho).ideal.support : Set E.curve.left).Nonempty := by
  rw [FiniteSubgroup.ideal, Scheme.Hom.support_ker]
  exact ⟨_, subset_closure ⟨(E.rationalCyclicGenerator P ho).left
    (IsLocalRing.closedPoint K), rfl⟩⟩

variable [SmoothOfRelativeDimension 1 E.curve.hom] [GeometricallyIntegral E.curve.hom]

/-- The actual rational cyclic subgroup divisor is relatively ample. -/
theorem rationalCyclicSubgroup_isAmple : (E.rationalCyclicSubgroup P ho).IsAmple := by
  have : IsProper E.curve.hom := E.family.family.1
  let H := E.rationalCyclicSubgroup P ho
  have hI := (E.rationalCyclicGenerator_isCartierGenerator P ho).2.1.1
  have : IsFinite (H.ideal.subschemeι ≫ E.curve.hom) := H.ideal_degree.1
  exact ⟨hI, (FCurve.smooth_divisor_relativeAmple_iff_nonempty E.curve.hom hI).mpr
    (E.rationalCyclicSubgroup_support_nonempty P ho)⟩

/-- The rational exact-order point gives actual ample cyclic level data. -/
def rationalCyclicLevel : ampleCyclicLevels (Spec (.of K)) n :=
  ⟨⟨E, E.rationalCyclicSubgroup P ho⟩,
    (E.rationalCyclicGenerator_isCartierGenerator P ho).isCyclic _,
    E.rationalCyclicSubgroup_isAmple P ho⟩

/-- The rational point's class in the ample cyclic moduli presheaf. -/
def rationalCyclicModuliPoint : ampleCyclicClasses (Spec (.of K)) n :=
  Quotient.mk _ (E.rationalCyclicLevel P ho)

/-- Forgetting the level conditions retains the constructed finite etale subgroup. -/
theorem rationalCyclicModuliPoint_forget :
    ampleCyclicClassesForget (Spec (.of K)) n (E.rationalCyclicModuliPoint P ho) =
      Quotient.mk (compatibleIsoSetoid (Spec (.of K)) n)
        ⟨E, E.rationalCyclicSubgroup P ho⟩ := rfl

end FLT.Mazur.GeneralizedEllipticCurve
