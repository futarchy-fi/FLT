/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ProartinianQuotients

/-!
# A common finite quotient for finitely many discrete parameters

Finiteness of the maps to a discrete test object produces one proper open
ideal through which all those maps factor. This uses the given topology;
it does not identify it with the maximal-ideal-adic topology.
-/

@[expose] public noncomputable section
open CategoryTheory IsLocalRing
namespace Deformation.ProartinianCat

variable {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
  (A B : ProartinianCat O)

/-- The common kernel of all parameters with the specified target. -/
def parameterKernel : Ideal A := ⨅ f : A ⟶ B, RingHom.ker f.hom.toRingHom

omit [IsLocalRing O] [Finite (ResidueField O)] in
/-- A finite family of discrete parameters has an open common kernel. -/
theorem parameterKernel_isOpen [Finite (A ⟶ B)] [DiscreteTopology B] :
    IsOpen (parameterKernel A B : Set A) := by
  have heq : (parameterKernel A B : Set A) =
      ⋂ f : A ⟶ B, f.hom ⁻¹' {0} := by ext; simp [parameterKernel]
  rw [heq]
  exact isOpen_iInter_of_finite fun f ↦ (isOpen_discrete {0}).preimage f.hom.cont

/-- Intersecting with the maximal ideal makes the common quotient proper even
when there are no parameters. -/
def parameterOpenIdeal [Finite (A ⟶ B)] [DiscreteTopology B] : OpenIdeal A :=
  OrderDual.toDual ⟨parameterKernel A B ⊓ maximalIdeal A,
    (parameterKernel_isOpen A B).inter isOpen_maximalIdeal_of_isProartinian,
    ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top inf_le_right⟩

omit [IsLocalRing O] [Finite (ResidueField O)] in
/-- The common proper open ideal is killed by each parameter. -/
theorem parameterOpenIdeal_le_ker [Finite (A ⟶ B)] [DiscreteTopology B]
    (f : A ⟶ B) : OpenIdeal.ideal (parameterOpenIdeal A B) ≤
      RingHom.ker f.hom.toRingHom :=
  inf_le_left.trans (iInf_le _ f)

/-- Descend a parameter to any proper open quotient that it kills. -/
def descendOpenIdeal (I : OpenIdeal A) (f : A ⟶ B)
    (hI : OpenIdeal.ideal I ≤ RingHom.ker f.hom.toRingHom) :
    openIdealQuotient A I ⟶ B where
  hom :=
    { toAlgHom := Ideal.Quotient.liftₐ (OpenIdeal.ideal I) f.hom.toAlgHom hI
      cont := by
        change Continuous (Ideal.Quotient.liftₐ (OpenIdeal.ideal I) f.hom.toAlgHom hI)
        exact continuous_of_discreteTopology }

/-- Descending and precomposing recovers the original parameter. -/
@[simp] theorem quotient_descendOpenIdeal (I : OpenIdeal A) (f : A ⟶ B)
    (hI : OpenIdeal.ideal I ≤ RingHom.ker f.hom.toRingHom) :
    openIdealQuotientHom A I ≫ descendOpenIdeal A B I f hI = f := by
  apply hom_ext
  ext
  rfl

/-- The common finite quotient represents exactly the same parameters to B. -/
def parameterQuotientEquiv [Finite (A ⟶ B)] [DiscreteTopology B] :
    (openIdealQuotient A (parameterOpenIdeal A B) ⟶ B) ≃ (A ⟶ B) where
  toFun g := openIdealQuotientHom A (parameterOpenIdeal A B) ≫ g
  invFun f := descendOpenIdeal A B _ f (parameterOpenIdeal_le_ker A B f)
  left_inv g := by
    apply hom_ext
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  right_inv f := quotient_descendOpenIdeal A B _ f _

end Deformation.ProartinianCat
