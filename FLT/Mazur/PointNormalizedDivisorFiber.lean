/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointNormalizedLineBundle
public import FLT.Mazur.CartierAbelRelativeBaseChange

/-!
# Full relative divisors and pointed normalized line classes

Normalize the actual positive divisor bundle at the section. Its kernel
class is the pointed Abel map. Equality of these classes is equivalent to
the original relative Abel equality, retaining the full Cartier ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- The pointed class of the actual positive divisor line with its constructed rigidification. -/
def pointedDivisorClass (D : Divisor X) : (SchemePicard.pullback e).ker :=
  rigidifiedBundleKernel e (pointNormalizedRigidified f e
    (divisorLineBundle D.val D.property) D.property.divisorLineBundle_locallyFreeRankOne he)

/-- The constructed pointed class is the original Abel class under normalization. -/
theorem pointedDivisorClass_eq (D : Divisor X) :
    pointedDivisorClass f e he D = relativeKernelEquiv f e he (abel f D) := by
  apply Subtype.ext
  exact pointNormalizedLine_class f e _ _

/-- Equality in the pointed fiber is exactly equality in the original relative Abel fiber. -/
theorem pointedDivisorClass_eq_iff (D : Divisor X) (L : X.Modules)
    (hL : LocallyFreeRankOne L) :
    pointedDivisorClass f e he D = normalizeToKernel f e he (mk L hL) ↔
      abel f D = relativeClass f (mk L hL) := by
  rw [pointedDivisorClass_eq]
  change relativeKernelEquiv f e he (abel f D) =
    relativeKernelEquiv f e he (relativeClass f (mk L hL)) ↔ _
  exact (relativeKernelEquiv f e he).injective.eq_iff

/-- The pointed fiber retains the original full divisor and its flatness over the base. -/
def PointedRelativeFiber (L : X.Modules) (hL : LocallyFreeRankOne L) :=
  {D : Divisor X // Flat (D.val.subschemeι ≫ f) ∧
    pointedDivisorClass f e he D = normalizeToKernel f e he (mk L hL)}

/-- The actual relative Abel fiber and pointed normalized fiber have the same full divisors. -/
def relativePointedFiberEquiv (L : X.Modules) (hL : LocallyFreeRankOne L) :
    RelativeFiber f L hL ≃ PointedRelativeFiber f e he L hL where
  toFun D := ⟨D.val.val, D.property,
    (pointedDivisorClass_eq_iff f e he D.val.val L hL).mpr D.val.property⟩
  invFun D := ⟨⟨D.val, (pointedDivisorClass_eq_iff f e he D.val L hL).mp D.property.2⟩,
    D.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The pointed correspondence retains the entire ideal, including multiplicities and nilpotents. -/
lemma relativePointedFiberEquiv_ideal (L : X.Modules) (hL : LocallyFreeRankOne L)
    (D : RelativeFiber f L hL) :
    (relativePointedFiberEquiv f e he L hL D).val.val = D.val.val.val := rfl

/-- A pointed fiber element supplies an actual isomorphism of the normalized line sheaves. -/
theorem pointedRelativeFiber_lineIso (L : X.Modules) (hL : LocallyFreeRankOne L)
    (D : PointedRelativeFiber f e he L hL) :
    Nonempty (pointNormalizedLine f e (divisorLineBundle D.val.val D.val.property) ≅
      pointNormalizedLine f e L) := by
  apply (mk_eq_mk_iff (pointNormalizedLine_rankOne f e _
    D.val.property.divisorLineBundle_locallyFreeRankOne)
      (pointNormalizedLine_rankOne f e L hL)).mp
  exact (congrArg Subtype.val D.property.2).trans (pointNormalizedLine_class f e L hL).symm

/-- The normalized divisor line is isomorphic with preservation of the actual rigidifications. -/
theorem pointedRelativeFiber_rigidifiedIso (L : X.Modules) (hL : LocallyFreeRankOne L)
    (D : PointedRelativeFiber f e he L hL) :
    Nonempty (LineSheafSectionRigidity.RigidifiedIso e
      (pointNormalizedLinePointIso f e (divisorLineBundle D.val.val D.val.property)
        D.val.property.divisorLineBundle_locallyFreeRankOne he)
      (pointNormalizedLinePointIso f e L hL he)) := by
  apply (LineSheafSectionRigidity.rigidifiedIso_nonempty_iff f e he
    (pointNormalizedLine_rankOne f e _ D.val.property.divisorLineBundle_locallyFreeRankOne)
    _ _).mpr
  exact pointedRelativeFiber_lineIso f e he L hL D

end FLT.Mazur.CartierAbel
