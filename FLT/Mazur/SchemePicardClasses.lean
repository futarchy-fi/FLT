/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierTensorRank
public import FLT.Mazur.ModuleSheafTensorAssociator

/-!
# Isomorphism classes of line bundles on a scheme

Tensor multiplication on actual locally free rank-one module sheaves descends
to their isomorphism classes. This file constructs the commutative monoid;
duality supplies inverses separately.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.SchemePicard

open FCurve

variable (X : Scheme.{u})

/-- An actual locally free rank-one module sheaf. -/
abbrev LineBundle := {M : X.Modules // LocallyFreeRankOne M}

/-- Line bundles are identified precisely by module-sheaf isomorphisms. -/
def lineBundleSetoid : Setoid (LineBundle X) where
  r M N := Nonempty (M.val ≅ N.val)
  iseqv := ⟨fun M ↦ ⟨Iso.refl M.val⟩,
    fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e ≪≫ f⟩⟩

/-- The Picard classes of a scheme, before any universe shrinking. -/
def Pic := Quotient (lineBundleSetoid X)

variable {X}

/-- The class of a line bundle. -/
def mk (M : X.Modules) (hM : LocallyFreeRankOne M) : Pic X :=
  Quotient.mk (lineBundleSetoid X) ⟨M, hM⟩

/-- Equality of classes is equivalent to an actual isomorphism of sheaves. -/
theorem mk_eq_mk_iff {M N : X.Modules}
    (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) :
    mk M hM = mk N hN ↔ Nonempty (M ≅ N) := Quotient.eq

/-- Isomorphic line bundles have equal classes. -/
theorem mk_eq_of_iso {M N : X.Modules}
    (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) (e : M ≅ N) :
    mk M hM = mk N hN := (mk_eq_mk_iff hM hN).mpr ⟨e⟩

/-- Every Picard class is represented by an actual line bundle. -/
@[elab_as_elim]
theorem inductionOn {P : Pic X → Prop} (a : Pic X)
    (h : ∀ (M : X.Modules) (hM : LocallyFreeRankOne M), P (mk M hM)) : P a :=
  Quotient.inductionOn a fun M ↦ h M.val M.property

instance : One (Pic X) := ⟨mk (structureModule X) structureModule_locallyFreeRankOne⟩

instance : Mul (Pic X) where
  mul a b := Quotient.liftOn₂ a b
    (fun M N ↦ mk (ModuleSheafTensor.tensor M.val N.val) (M.property.tensor N.property))
    (fun _ _ _ _ ⟨e⟩ ⟨f⟩ ↦
      mk_eq_of_iso _ _ (ModuleSheafTensor.congr e f))

/-- Tensor product represents multiplication of classes. -/
@[simp]
theorem mk_tensor (M N : X.Modules) (hM : LocallyFreeRankOne M)
    (hN : LocallyFreeRankOne N) :
    mk (ModuleSheafTensor.tensor M N) (hM.tensor hN) = mk M hM * mk N hN := rfl

/-- The structure sheaf represents the identity class. -/
@[simp]
theorem mk_structure : mk (structureModule X) structureModule_locallyFreeRankOne =
    (1 : Pic X) := rfl

instance : CommMonoid (Pic X) where
  mul_assoc a b c := by
    induction a using inductionOn with | h M hM =>
      induction b using inductionOn with | h N hN =>
        induction c using inductionOn with | h L hL =>
          exact mk_eq_of_iso _ _ (ModuleSheafTensorAssociator.associator M N L)
  one_mul a := by
    induction a using inductionOn with | h M hM =>
      exact mk_eq_of_iso _ _ (ModuleSheafTensor.leftUnitor M)
  mul_one a := by
    induction a using inductionOn with | h M hM =>
      exact mk_eq_of_iso _ _ (ModuleSheafTensorAssociator.comm M _ ≪≫
        ModuleSheafTensor.leftUnitor M)
  mul_comm a b := by
    induction a using inductionOn with | h M hM =>
      induction b using inductionOn with | h N hN =>
        exact mk_eq_of_iso _ _ (ModuleSheafTensorAssociator.comm M N)

/-- The neutral class consists exactly of globally trivial line bundles. -/
theorem mk_eq_one_iff (M : X.Modules) (hM : LocallyFreeRankOne M) :
    mk M hM = 1 ↔ Nonempty (M ≅ structureModule X) :=
  mk_eq_mk_iff hM structureModule_locallyFreeRankOne

end FLT.Mazur.SchemePicard
