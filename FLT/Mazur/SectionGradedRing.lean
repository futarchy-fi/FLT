/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedAssociativity
public import Mathlib.Algebra.DirectSum.Ring

/-!
# The ring of all tensor-power sections

The multiplication is the existing bilinear product on the full direct sum.
This ring exists for every module sheaf; commutativity needs a line-bundle
hypothesis and is a separate result.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedSum
open SectionGradedMultiplication
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)

/-- Transport of a degree does not change the associated homogeneous element. -/
lemma sigma_cast {m n : ℕ} (h : m = n) (s : Piece L U m) :
    (⟨n, cast L h U s⟩ : GradedMonoid (Piece L U)) = ⟨m, s⟩ := by
  subst n
  rfl

/-- The tensor pairing is graded multiplication. -/
instance gradedMul : GradedMonoid.GMul (Piece L U) where
  mul {m n} s t := mul L U m n s t

/-- The structure sheaf's unit is a homogeneous element of degree zero. -/
instance gradedOne : GradedMonoid.GOne (Piece L U) where
  one := (1 : Γ(X, U))

/-- All tensor degrees form a graded ring under the actual sheaf tensor product. -/
instance gradedRing : DirectSum.GRing (Piece L U) where
  __ := gradedMul L U
  __ := gradedOne L U
  mul_zero {i j} s := (mul L U i j s).map_zero
  zero_mul {i j} t := LinearMap.congr_fun (map_zero (mul L U i j)) t
  mul_add := SectionGradedMultiplication.mul_add L U _ _
  add_mul := SectionGradedMultiplication.add_mul L U _ _
  one_mul := by
    rintro ⟨n, s⟩
    change (⟨0 + n, mul L U 0 n (1 : Γ(X, U)) s⟩ : GradedMonoid (Piece L U)) = ⟨n, s⟩
    rw [SectionGradedMultiplication.zero_mul, one_smul]
    exact sigma_cast L U _ s
  mul_one := by
    rintro ⟨n, s⟩
    change (⟨n + 0, mul L U n 0 s (1 : Γ(X, U))⟩ : GradedMonoid (Piece L U)) = ⟨n, s⟩
    rw [SectionGradedMultiplication.mul_zero, one_smul]
    rfl
  mul_assoc := by
    rintro ⟨m, s⟩ ⟨n, t⟩ ⟨k, v⟩
    change (⟨(m + n) + k, mul L U (m + n) k (mul L U m n s t) v⟩ :
      GradedMonoid (Piece L U)) = ⟨m + (n + k), mul L U m (n + k) s (mul L U n k t v)⟩
    rw [SectionGradedMultiplication.mul_assoc]
    exact sigma_cast L U _ _
  natCast n := (n : Γ(X, U))
  natCast_zero := by exact (Nat.cast_zero (R := Γ(X, U)))
  natCast_succ n := by exact (Nat.cast_succ (R := Γ(X, U)) n)
  intCast n := (n : Γ(X, U))
  intCast_ofNat n := by exact (Int.cast_natCast (R := Γ(X, U)) n)
  intCast_negSucc_ofNat n := by exact (Int.cast_negSucc (R := Γ(X, U)) n)

/-- The full direct sum inherits its ring structure from tensor-degree multiplication. -/
instance sectionRing : Ring (Sections L U) := DirectSum.ring _

/-- The ring multiplication on homogeneous inputs is the specified bilinear product. -/
lemma mul_of (m n : ℕ) (s : Piece L U m) (t : Piece L U n) :
    of L U m s * of L U n t = of L U (m + n) (mul L U m n s t) :=
  DirectSum.of_mul_of s t

/-- The ring multiplication agrees with the previously constructed full product. -/
lemma mul_eq_product (a b : Sections L U) : a * b = product L U a b := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m s =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | of n t => exact (mul_of L U m n s t).trans (product_of L U m n s t).symm
    | add b c hb hc => simp only [_root_.mul_add, map_add, hb, hc]
  | add a c ha hc => simp only [_root_.add_mul, map_add, LinearMap.add_apply, ha, hc]

/-- The ring's unit is the previously specified degree-zero section. -/
lemma one_eq_unit : (1 : Sections L U) = unit L U := rfl

/-- The bilinear full product is associative on arbitrary finite sums. -/
lemma product_assoc (a b c : Sections L U) :
    product L U (product L U a b) c = product L U a (product L U b c) := by
  simp only [← mul_eq_product, _root_.mul_assoc]

/-- Restriction is a unital ring homomorphism on the full section ring. -/
def restrictRingHom {V : X.Opens} (i : U ⟶ V) : Sections L V →+* Sections L U where
  __ := restrict L i
  map_one' := by
    change restrict L i (of L V 0 (1 : Γ(X, V))) = of L U 0 (1 : Γ(X, U))
    rw [restrict_of]
    congr 1
    exact (X.presheaf.map i.op).hom.map_one
  map_mul' a b := by
    simp only [mul_eq_product]
    exact restrict_product L i a b

end FLT.Mazur.SectionGradedSum
