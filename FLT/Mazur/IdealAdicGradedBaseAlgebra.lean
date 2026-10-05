/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedBaseProduct

/-!
# The associated-graded base algebra acts on the extended graded algebra

For an affine base open, the actual comparison extends to a unital ring
homomorphism on all degrees. Restriction of scalars along this homomorphism
gives the base algebra action, without any flatness or base-change isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.IdealAdicGradedSections

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U : Y.affineOpens)

/-- The canonical base comparison extended to all homogeneous degrees. -/
def sumMap : IdealAdicGradedSections.Sections J U.1 →+
    IdealAdicGradedSections.Sections (J.comap f) (f ⁻¹ᵁ U.1) :=
  DirectSum.toAddMonoid (fun n ↦
    (DirectSum.of (Piece (J.comap f) (f ⁻¹ᵁ U.1)) n).comp ((gradedMap J f n).app U.1).hom)

/-- The direct-sum comparison retains its actual homogeneous components. -/
lemma sumMap_of (n : ℕ) (s : Piece J U.1 n) :
    sumMap J f U (of J U.1 n s) = of (J.comap f) (f ⁻¹ᵁ U.1) n (pull J f n U.1 s) :=
  DirectSum.toAddMonoid_of _ n s

/-- The base comparison is a unital ring homomorphism on the full graded algebras. -/
def ringHom : IdealAdicGradedSections.Sections J U.1 →+*
    IdealAdicGradedSections.Sections (J.comap f) (f ⁻¹ᵁ U.1) where
  __ := sumMap J f U
  map_one' := by
    change sumMap J f U 1 = 1
    rw [one_eq, sumMap_of, pull_scalar, map_one, one_eq]
  map_mul' a b := by
    change sumMap J f U (a * b) = sumMap J f U a * sumMap J f U b
    induction a using DirectSum.induction_on with
    | zero => simp
    | of m s =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | of n t =>
        change sumMap J f U (of J U.1 m s * of J U.1 n t) =
          sumMap J f U (of J U.1 m s) * sumMap J f U (of J U.1 n t)
        rw [mul_of, sumMap_of, sumMap_of, sumMap_of, mul_of, pull_mul]
      | add b c hb hc => simp only [_root_.mul_add, map_add, hb, hc]
    | add a c ha hc => simp only [_root_.add_mul, map_add, ha, hc]

/-- Restriction of scalars along the actual associated-graded base comparison. -/
@[instance_reducible]
def baseAlgebra : Algebra (IdealAdicGradedSections.Sections J U.1)
    (IdealAdicGradedSections.Sections (J.comap f) (f ⁻¹ᵁ U.1)) :=
  (ringHom J f U).toAlgebra

/-- The action of a homogeneous base coefficient is actual graded multiplication. -/
lemma base_smul_of (a b : ℕ) (s : Piece J U.1 a)
    (t : Piece (J.comap f) (f ⁻¹ᵁ U.1) b) :
    let := baseAlgebra J f U
    of J U.1 a s • of (J.comap f) (f ⁻¹ᵁ U.1) b t =
      of (J.comap f) (f ⁻¹ᵁ U.1) (a + b)
        (mul (J.comap f) (f ⁻¹ᵁ U.1) a b (pull J f a U.1 s) t) := by
  let := baseAlgebra J f U
  change ringHom J f U (of J U.1 a s) * of (J.comap f) (f ⁻¹ᵁ U.1) b t = _
  change sumMap J f U (of J U.1 a s) * of (J.comap f) (f ⁻¹ᵁ U.1) b t = _
  rw [sumMap_of, mul_of]

end FLT.Mazur.IdealAdicGradedPullback
