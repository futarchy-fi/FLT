/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedRing

/-!
# Tensor powers and powers in the section ring

The exponent-multiplication isomorphism takes the pure power of a section
of degree `d` to its actual power in the full graded section ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedPowers
open FCurve ModuleLineBundleTensorPullback ModuleSheafTensor
open SectionGradedMultiplication SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)

/-- Degree transport does not change a section's inclusion in the full ring. -/
lemma of_cast {m n : ℕ} (h : m = n) (s : Piece L U m) :
    of L U n (cast L h U s) = of L U m s := by
  subst n
  rfl

/-- The exponent-multiplication isomorphism on a pure successor tensor. -/
lemma mulIso_cons (d n : ℕ) (s : Piece L U d)
    (t : Γ(tensorPower (tensorPower L d) n, U)) :
    (tensorPowerMulIso L d (n + 1)).hom.app U (pure _ _ U s t) =
      cast L (by rw [Nat.mul_succ, Nat.add_comm] : d + d * n = d * (n + 1)) U
        (mul L U d (d * n) s ((tensorPowerMulIso L d n).hom.app U t)) := by
  let h : d + d * n = d * (n + 1) := by rw [Nat.mul_succ, Nat.add_comm]
  have hm := ModuleSheafTensor.map_pure (𝟙 (tensorPower L d))
    (tensorPowerMulIso L d n).hom U s t
  have hm' : (ModuleSheafTensor.map (𝟙 (tensorPower L d))
      (tensorPowerMulIso L d n).hom).app U (pure _ _ U s t) =
      pure _ _ U s ((tensorPowerMulIso L d n).hom.app U t) := hm
  exact congrArg (fun z ↦ cast L h U ((tensorPowerAddIso L d (d * n)).hom.app U z)) hm'


/-- A pure nested tensor power is exactly a homogeneous ring power. -/
lemma of_tensorPower (d : ℕ) (s : Piece L U d) (n : ℕ) :
    of L U (d * n) ((tensorPowerMulIso L d n).hom.app U
      (tensorPowerSection (tensorPower L d) U s n)) = (of L U d s) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tensorPowerSection, mulIso_cons, of_cast, ← mul_of, ih, pow_succ']

end FLT.Mazur.SectionGradedPowers
