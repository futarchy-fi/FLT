/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedSections
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# The actual ideal-adic graded section algebra

The direct sum includes every nonnegative degree. Its commutative algebra
structure is induced by the actual quotient sheaves and their proved laws.
In particular this constructs the base algebra on an affine base scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) (U : X.Opens)

/-- The direct sum of sections of all actual ideal-adic graded pieces. -/
abbrev Sections := ⨁ n : ℕ, Piece I U n

/-- Homogeneous insertion into the full graded algebra. -/
abbrev of (n : ℕ) : Piece I U n →ₗ[Γ(X, U)] Sections I U :=
  DirectSum.lof Γ(X, U) ℕ (Piece I U) n

omit [IsLocallyNoetherian X] in
/-- Degree transport preserves the represented homogeneous element. -/
lemma sigma_cast {a b : ℕ} (h : a = b) (s : Piece I U a) :
    (⟨b, cast I h U s⟩ : GradedMonoid (Piece I U)) = ⟨a, s⟩ := by
  subst b
  rfl

/-- The graded multiplication is the quotient-sheaf product. -/
instance gradedMul : GradedMonoid.GMul (Piece I U) where
  mul {a b} s t := mul I U a b s t

/-- The unit is the image of the structure sheaf's unit in degree zero. -/
instance gradedOne : GradedMonoid.GOne (Piece I U) where
  one := scalar I U 1

set_option maxHeartbeats 800000 in
-- Checking all graded ring fields unfolds the quotient-sheaf section instances repeatedly.
/-- The actual associated-graded pieces form a commutative graded ring. -/
instance gradedCommRing : DirectSum.GCommRing (Piece I U) where
  __ := gradedMul I U
  __ := gradedOne I U
  mul_zero {i j} s := (mul I U i j s).map_zero
  zero_mul {i j} t := LinearMap.congr_fun (map_zero (mul I U i j)) t
  mul_add {i j} s t v := (mul I U i j s).map_add t v
  add_mul {i j} s t v := LinearMap.congr_fun (map_add (mul I U i j) s t) v
  one_mul := by
    rintro ⟨n, s⟩
    change (⟨0 + n, mul I U 0 n (scalar I U 1) s⟩ : GradedMonoid (Piece I U)) = ⟨n, s⟩
    rw [scalar_mul, one_smul]
    exact sigma_cast I U _ s
  mul_one := by
    rintro ⟨n, s⟩
    change (⟨n + 0, mul I U n 0 s (scalar I U 1)⟩ : GradedMonoid (Piece I U)) = ⟨n, s⟩
    rw [mul_scalar, one_smul]
    rfl
  mul_assoc := by
    rintro ⟨a, s⟩ ⟨b, t⟩ ⟨c, v⟩
    change (⟨a + b + c, mul I U (a + b) c (mul I U a b s t) v⟩ :
      GradedMonoid (Piece I U)) = ⟨a + (b + c), mul I U a (b + c) s (mul I U b c t v)⟩
    exact (congrArg (fun w ↦ (⟨a + b + c, w⟩ : GradedMonoid (Piece I U)))
      (IdealAdicGradedSections.mul_assoc I a b c U s t v)).trans (sigma_cast I U _ _)
  mul_comm := by
    rintro ⟨a, s⟩ ⟨b, t⟩
    change (⟨a + b, mul I U a b s t⟩ : GradedMonoid (Piece I U)) =
      ⟨b + a, mul I U b a t s⟩
    exact (congrArg (fun w ↦ (⟨a + b, w⟩ : GradedMonoid (Piece I U)))
      (IdealAdicGradedSections.mul_comm I a b U s t)).trans (sigma_cast I U _ _)
  natCast n := scalar I U n
  natCast_zero := by simp
  natCast_succ n := by
    change scalar I U ((n + 1 : ℕ) : Γ(X, U)) = scalar I U n + scalar I U 1
    rw [Nat.cast_succ, map_add]
  intCast n := scalar I U n
  intCast_ofNat n := by simp
  intCast_negSucc_ofNat n := by simp

/-- The direct sum has the commutative ring structure of the actual graded product. -/
instance sectionsCommRing : CommRing (Sections I U) := DirectSum.commRing _

/-- Homogeneous multiplication agrees with the sheaf product. -/
lemma mul_of (a b : ℕ) (s : Piece I U a) (t : Piece I U b) :
    of I U a s * of I U b t = of I U (a + b) (mul I U a b s t) :=
  DirectSum.of_mul_of s t

omit [IsLocallyNoetherian X] in
/-- The unit is the homogeneous image of the structure sheaf's unit. -/
lemma one_eq : (1 : Sections I U) = of I U 0 (scalar I U 1) := rfl

/-- Structure-sheaf scalars give the graded algebra structure. -/
instance gradedScalarAlgebra : DirectSum.GAlgebra Γ(X, U) (Piece I U) where
  toFun := (scalar I U).toAddMonoidHom
  map_one := rfl
  map_mul r s := by
    change (⟨0, scalar I U (r * s)⟩ : GradedMonoid (Piece I U)) =
      ⟨0 + 0, mul I U 0 0 (scalar I U r) (scalar I U s)⟩
    rw [scalar_mul]
    congr 1
    exact (scalar I U).map_smul r s
  commutes r := by
    rintro ⟨n, s⟩
    change (⟨0 + n, mul I U 0 n (scalar I U r) s⟩ : GradedMonoid (Piece I U)) =
      ⟨n + 0, mul I U n 0 s (scalar I U r)⟩
    rw [scalar_mul, mul_scalar]
    exact sigma_cast I U _ _
  smul_def r := by
    rintro ⟨n, s⟩
    change (⟨n, r • s⟩ : GradedMonoid (Piece I U)) =
      ⟨0 + n, mul I U 0 n (scalar I U r) s⟩
    rw [scalar_mul]
    exact (sigma_cast I U _ _).symm

/-- Restriction acts on each actual graded quotient sheaf. -/
def restrict {V : X.Opens} (i : U ⟶ V) : Sections I V →+ Sections I U :=
  DirectSum.toAddMonoid (fun n ↦ (DirectSum.of (Piece I U) n).comp
    ((IdealAdicQuotient.idealGraded I n).presheaf.map i.op).hom)

/-- Restriction preserves homogeneous insertion. -/
lemma restrict_of {V : X.Opens} (i : U ⟶ V) (n : ℕ) (s : Piece I V n) :
    restrict I U i (of I V n s) =
      of I U n ((IdealAdicQuotient.idealGraded I n).presheaf.map i.op s) :=
  DirectSum.toAddMonoid_of _ n s

/-- Restriction is a unital ring homomorphism on the full graded algebra. -/
def restrictRingHom {V : X.Opens} (i : U ⟶ V) : Sections I V →+* Sections I U where
  __ := restrict I U i
  map_one' := by
    change restrict I U i 1 = 1
    rw [one_eq, restrict_of, scalar_restrict, map_one, one_eq]
  map_mul' a b := by
    change restrict I U i (a * b) = restrict I U i a * restrict I U i b
    induction a using DirectSum.induction_on with
    | zero => simp
    | of m s =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | of n t =>
        change restrict I U i (of I V m s * of I V n t) =
          restrict I U i (of I V m s) * restrict I U i (of I V n t)
        rw [mul_of, restrict_of, restrict_of, restrict_of, mul_of, mul_restrict]
      | add b c hb hc => simp only [_root_.mul_add, map_add, hb, hc]
    | add a c ha hc => simp only [_root_.add_mul, map_add, ha, hc]

end FLT.Mazur.IdealAdicGradedSections
