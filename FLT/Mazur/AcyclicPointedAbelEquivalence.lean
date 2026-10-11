/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicRankOneLineCondition

/-!
# The acyclic rank-one pointed Abel correspondence

Full relative Cartier divisors whose positive lines are acyclic with rank-one
direct image correspond to normalized Picard classes with those intrinsic
conditions. Surjectivity constructs a divisor from any actual line
representative. This is a correspondence of sets, not a representing scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- Full relative divisors with intrinsic acyclic rank-one positive line. -/
def AcyclicRankOneRelativeDivisor :=
  {D : Divisor X // Flat (D.val.subschemeι ≫ f) ∧
    AcyclicRankOne f (divisorLineBundle D.val D.property)}

/-- Normalized classes admitting an actual line with the intrinsic cohomological conditions. -/
def AcyclicRankOnePointedClass :=
  {c : (SchemePicard.pullback e).ker // ∃ (L : X.Modules) (hL : LocallyFreeRankOne L),
    mk L hL = c.val ∧ AcyclicRankOne f L}

/-- The pointed Abel map lands in the intrinsic acyclic rank-one classes. -/
def acyclicPointedAbel (D : AcyclicRankOneRelativeDivisor f) :
    AcyclicRankOnePointedClass f e := by
  let L := divisorLineBundle D.val.val D.val.property
  have hL := D.val.property.divisorLineBundle_locallyFreeRankOne
  refine ⟨pointedDivisorClass f e he D.val, pointNormalizedLine f e L,
    pointNormalizedLine_rankOne f e L hL, ?_,
      (acyclicRankOne_normalize f e L hL).mpr D.property.2⟩
  rfl

/-- This correspondence uses the original normalized Abel class of the actual full divisor. -/
lemma acyclicPointedAbel_class (D : AcyclicRankOneRelativeDivisor f) :
    (acyclicPointedAbel f e he D).val = pointedDivisorClass f e he D.val := rfl

/-- Equality of normalized classes determines the full relative divisor on the intrinsic locus. -/
theorem acyclicPointedAbel_injective [Surjective f] :
    Function.Injective (acyclicPointedAbel f e he) := by
  intro D E h
  apply Subtype.ext
  exact pointedDivisor_eq_of_class_eq f e he D.val E.val
    D.property.1 E.property.1 D.property.2.2 (congrArg Subtype.val h)

/-- Every intrinsic normalized class has a constructed full relative Cartier divisor. -/
theorem acyclicPointedAbel_surjective [IsLocallyNoetherian S]
    [IsProper f] [Flat f] [GeometricallyIntegral f] :
    Function.Surjective (acyclicPointedAbel f e he) := by
  rintro ⟨c, L, hL, hc, hA⟩
  obtain ⟨D⟩ := acyclicRankOne_relativeFiber_nonempty f L hL hA
  let E := relativePointedFiberEquiv f e he L hL D
  have hE := acyclicRankOne_divisor_of_pointedFiber f e he L hL hA E
  refine ⟨⟨E.val, E.property.1, hE⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hclass := congrArg Subtype.val E.property.2
  change (pointedDivisorClass f e he E.val).val = normalize f e (mk L hL) at hclass
  exact hclass.trans ((congrArg (normalize f e) hc).trans
    (normalize_of_mem_kernel f e c.val c.property))

/-- Full divisors and normalized acyclic rank-one classes are equivalent on the actual family. -/
def acyclicPointedAbelEquiv [IsLocallyNoetherian S]
    [IsProper f] [Flat f] [GeometricallyIntegral f] :
    AcyclicRankOneRelativeDivisor f ≃ AcyclicRankOnePointedClass f e :=
  Equiv.ofBijective (acyclicPointedAbel f e he)
    ⟨acyclicPointedAbel_injective f e he, acyclicPointedAbel_surjective f e he⟩

/-- The equivalence is the actual normalized positive-divisor-line map. -/
lemma acyclicPointedAbelEquiv_class [IsLocallyNoetherian S]
    [IsProper f] [Flat f] [GeometricallyIntegral f]
    (D : AcyclicRankOneRelativeDivisor f) :
    (acyclicPointedAbelEquiv f e he D).val = pointedDivisorClass f e he D.val := rfl

end FLT.Mazur.CartierAbel
