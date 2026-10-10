/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChart

/-!
# Inverting the original denominator in a Rees fraction chart

The fraction chart embeds in A[1/f]. Inverting its original element f gives
exactly A[1/f], including when A has zero divisors. The comparison retains A.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.BlowupFractionChart

set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [CommRing A] (I : Ideal A) (f : A)

/-- The original denominator, as an element of the actual fraction chart. -/
def denominator : chart I f := algebraMap A (chart I f) f

/-- The open of the fraction chart where the original denominator is inverted. -/
abbrev DenominatorOpen := Localization.Away (denominator I f)

/-- The embedding extends after inverting the original denominator. -/
def toOriginalOpen : DenominatorOpen I f →ₐ[A] Localization.Away f :=
  IsLocalization.Away.liftAlgHom (denominator I f)
    (f := (chart I f).val) (IsLocalization.Away.algebraMap_isUnit f)

/-- The extended embedding agrees with the original inclusion on the chart. -/
@[simp] theorem toOriginalOpen_base (a : chart I f) :
    toOriginalOpen I f (algebraMap (chart I f) (DenominatorOpen I f) a) = a := by
  rw [toOriginalOpen, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- Extending this subalgebra inclusion to the denominator open stays injective. -/
theorem toOriginalOpen_injective : Function.Injective (toOriginalOpen I f) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (denominator I f)) (toOriginalOpen I f).toRingHom).mpr
  intro a b
  constructor
  · exact congrArg (toOriginalOpen I f)
  · intro h
    have hab : (a : Localization.Away f) = b := by
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        toOriginalOpen_base] using h
    exact congrArg (algebraMap (chart I f) (DenominatorOpen I f)) (Subtype.ext hab)

/-- The original principal localization maps back to the denominator open. -/
def fromOriginalOpen : Localization.Away f →ₐ[A] DenominatorOpen I f :=
  IsLocalization.Away.liftAlgHom f (f := Algebra.ofId A (DenominatorOpen I f)) (by
    change IsUnit (algebraMap A (DenominatorOpen I f) f)
    rw [IsScalarTower.algebraMap_apply A (chart I f) (DenominatorOpen I f)]
    exact IsLocalization.Away.algebraMap_isUnit (denominator I f))

/-- The extended inclusion has the explicit original-localization map as a right inverse. -/
theorem toOriginalOpen_comp_fromOriginalOpen :
    (toOriginalOpen I f).comp (fromOriginalOpen I f) = AlgHom.id A _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  ext

/-- The denominator open of the Rees fraction chart is the original principal open. -/
def denominatorOpenEquiv : DenominatorOpen I f ≃ₐ[A] Localization.Away f :=
  AlgEquiv.ofBijective (toOriginalOpen I f)
    ⟨toOriginalOpen_injective I f, fun z => ⟨fromOriginalOpen I f z,
      congrArg (fun k : Localization.Away f →ₐ[A] Localization.Away f => k z)
        (toOriginalOpen_comp_fromOriginalOpen I f)⟩⟩

/-- The comparison on chart functions is the original fraction inclusion. -/
@[simp] theorem denominatorOpenEquiv_base (a : chart I f) :
    denominatorOpenEquiv I f (algebraMap (chart I f) (DenominatorOpen I f) a) = a :=
  toOriginalOpen_base I f a

end FLT.Mazur.BlowupFractionChart
