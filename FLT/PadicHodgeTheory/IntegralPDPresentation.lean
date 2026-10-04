/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# An integral presentation with maps to arbitrary divided-power targets

Impose `γ₁(x)=x` on the divided-power algebra of an ideal. Every map to a
ring with divided powers factors through this quotient, including torsion
targets. A divided-power structure on this quotient, its comparison with the
embedded theta hull, and p-compatibility are separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PadicHodgeTheory
variable {A : Type*} [CommRing A] (I : Ideal A)

/-- Relations identifying degree-one divided powers with the original ideal. -/
def integralPDRelations : Ideal (DividedPowerAlgebra A I) :=
  Ideal.span (Set.range fun x : I ↦
    DividedPowerAlgebra.dp A 1 x - algebraMap A (DividedPowerAlgebra A I) x)

/-- The integral quotient presentation; no divided-power structure is presumed. -/
abbrev IntegralPDPresentation := DividedPowerAlgebra A I ⧸ integralPDRelations I

/-- The universal divided-power symbols in the quotient presentation. -/
def integralPDSymbol (n : ℕ) (x : I) : IntegralPDPresentation I :=
  Ideal.Quotient.mkₐ A (integralPDRelations I) (DividedPowerAlgebra.dp A n x)

/-- The quotient imposes the correct degree-one relation over the original base. -/
theorem integralPDSymbol_one (x : I) :
    integralPDSymbol I 1 x = algebraMap A (IntegralPDPresentation I) x := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (integralPDRelations I)
    (DividedPowerAlgebra.dp A 1 x - algebraMap A (DividedPowerAlgebra A I) x) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨x, rfl⟩)

/-- The factorial identities hold integrally in the presentation. -/
theorem integralPDSymbol_factorial (n : ℕ) (x : I) :
    (n.factorial : IntegralPDPresentation I) * integralPDSymbol I n x =
      algebraMap A (IntegralPDPresentation I) x ^ n := by
  have h := congrArg (Ideal.Quotient.mkₐ A (integralPDRelations I))
    (DividedPowerAlgebra.natFactorial_mul_dp_eq (R := A) n x)
  simp only [map_mul, map_natCast, map_pow] at h
  change (n.factorial : IntegralPDPresentation I) * integralPDSymbol I n x =
    integralPDSymbol I 1 x ^ n at h
  rwa [integralPDSymbol_one] at h

variable {B : Type*} [CommRing B] [Algebra A B] (J : Ideal B) (hJ : DividedPowers J)
  (hI : ∀ x : I, algebraMap A B x ∈ J)

/-- The ideal inclusion followed by the original coefficient map. -/
def integralPDIdealMap : I →ₗ[A] B := (Algebra.linearMap A B).comp I.subtype

/-- Every genuine PD target kills the degree-one relations, even in the presence of torsion. -/
theorem integralPDRelations_le_ker : integralPDRelations I ≤ RingHom.ker
    (DividedPowerAlgebra.lift hJ (integralPDIdealMap I) hI).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨x, rfl⟩
  change (DividedPowerAlgebra.lift hJ (integralPDIdealMap I) hI) _ = 0
  simp [integralPDIdealMap, hJ.dpow_one (hI x)]

/-- The constructed integral map to an arbitrary divided-power target. -/
def integralPDTargetMap : IntegralPDPresentation I →ₐ[A] B :=
  Ideal.Quotient.liftₐ (integralPDRelations I)
    (DividedPowerAlgebra.lift hJ (integralPDIdealMap I) hI)
    (integralPDRelations_le_ker I J hJ hI)

/-- The map sends every universal symbol to the target's actual divided power. -/
theorem integralPDTargetMap_symbol (n : ℕ) (x : I) :
    integralPDTargetMap I J hJ hI (integralPDSymbol I n x) =
      hJ.dpow n (algebraMap A B x) :=
  DividedPowerAlgebra.lift_apply_dp hJ hI n x

/-- Values on divided-power symbols uniquely determine a map from the presentation. -/
theorem integralPDPresentation_ext (f g : IntegralPDPresentation I →ₐ[A] B)
    (h : ∀ n x, f (integralPDSymbol I n x) = g (integralPDSymbol I n x)) : f = g := by
  have he : f.comp (Ideal.Quotient.mkₐ A (integralPDRelations I)) =
      g.comp (Ideal.Quotient.mkₐ A (integralPDRelations I)) :=
    DividedPowerAlgebra.algHom_ext h
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective A (integralPDRelations I) x
  exact DFunLike.congr_fun he y

/-- The constructed target map is the only map with the prescribed PD values. -/
theorem integralPDTargetMap_unique (f : IntegralPDPresentation I →ₐ[A] B)
    (hf : ∀ n x, f (integralPDSymbol I n x) = hJ.dpow n (algebraMap A B x)) :
    f = integralPDTargetMap I J hJ hI :=
  integralPDPresentation_ext I f _ (fun n x ↦
    (hf n x).trans (integralPDTargetMap_symbol I J hJ hI n x).symm)

end PadicHodgeTheory
