/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.CartierDualInvariants
public import FLT.GroupScheme.RaynaudFlatQuotient

/-!
# Descent of integral maps through finite-flat quotients

The faithfully flat torsor identifies quotient coordinates with invariant
functions. Every integral group morphism that kills the prescribed kernel
therefore descends uniquely, with its coordinate and point formulas retained.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct WithConv

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ]
    {A H Q J : FiniteFlatObject R}

/-- A morphism killing the kernel takes its coordinates into the quotient's image. -/
theorem FiniteFlatExtension.mapMemQuotientRange (E : FiniteFlatExtension A H Q)
    (f : H.Hom J)
    (hf : E.inclusion.toAlgHom.comp f.toAlgHom =
      (Algebra.ofId R A.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R J.model.CoordinateRing))
    (j : J.model.CoordinateRing) : ∃ q, E.quotient q = f j := by
  apply (E.exists_quotient_preimage_iff (f j)).mpr
  let c : H.model.CoordinateRing →ₐ[R] H.model.CoordinateRing ⊗[R] A.model.CoordinateRing :=
    (Algebra.TensorProduct.map (AlgHom.id R H.model.CoordinateRing) E.inclusion.toAlgHom).comp
      (Bialgebra.comulAlgHom R H.model.CoordinateRing)
  have hc : c = (toConv (includeLeft : H.model.CoordinateRing →ₐ[R]
      H.model.CoordinateRing ⊗[R] A.model.CoordinateRing) *
        toConv (includeRight.comp E.inclusion.toAlgHom)).ofConv := by
    dsimp [c]
    rw [HopfAlgebra.comulAlgHom_eq_conv_include, AlgHom.comp_convMul_distrib]
    congr 2
    ext x
    simp
  have he : c.comp f.toAlgHom = includeLeft.comp f.toAlgHom := by
    rw [hc, AlgHom.convMul_comp_bialgHom_distrib]
    have hz : (includeRight.comp E.inclusion.toAlgHom).comp f.toAlgHom =
        (1 : WithConv (J.model.CoordinateRing →ₐ[R]
          H.model.CoordinateRing ⊗[R] A.model.CoordinateRing)).ofConv := by
      rw [AlgHom.comp_assoc, hf]
      ext x
      simp
    rw [hz]
    simp
  exact AlgHom.congr_fun he j

/-- Descend an integral group map that kills the kernel of an integral extension. -/
def FiniteFlatExtension.descendHom (E : FiniteFlatExtension A H Q)
    (f : H.Hom J)
    (hf : E.inclusion.toAlgHom.comp f.toAlgHom =
      (Algebra.ofId R A.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R J.model.CoordinateRing)) : Q.Hom J := by
  let e := AlgEquiv.ofInjective E.quotient.toAlgHom E.quotient_injective
  let a := e.symm.toAlgHom.comp
    (f.toAlgHom.codRestrict E.quotient.toAlgHom.range (E.mapMemQuotientRange f hf))
  exact BialgHom.factorOfInjectiveOfFlat E.quotient E.quotient_injective f a (by
    ext j
    exact congrArg Subtype.val (e.apply_symm_apply _))

/-- The descended map composes with the given quotient to the original map. -/
theorem FiniteFlatExtension.descendHomComp (E : FiniteFlatExtension A H Q)
    (f : H.Hom J)
    (hf : E.inclusion.toAlgHom.comp f.toAlgHom =
      (Algebra.ofId R A.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R J.model.CoordinateRing)) :
    E.quotient.comp (E.descendHom f hf) = f := by
  ext j
  exact congrArg Subtype.val
    ((AlgEquiv.ofInjective E.quotient.toAlgHom E.quotient_injective).apply_symm_apply _)

/-- Faithful flatness makes descent through the quotient unique. -/
theorem FiniteFlatExtension.descendHomUnique (E : FiniteFlatExtension A H Q)
    (f : H.Hom J)
    (hf : E.inclusion.toAlgHom.comp f.toAlgHom =
      (Algebra.ofId R A.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R J.model.CoordinateRing))
    (g : Q.Hom J) (hg : E.quotient.comp g = f) : g = E.descendHom f hf := by
  ext j
  apply E.quotient_injective
  exact (DFunLike.congr_fun hg j).trans (DFunLike.congr_fun (E.descendHomComp f hf) j).symm

end ThreeAdicPlan
