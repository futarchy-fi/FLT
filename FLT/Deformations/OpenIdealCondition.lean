/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ProartinianQuotients
public import FLT.Deformations.Subfunctor

/-!
# Quotient conditions on a proartinian parameter ring

Maps killing a proper open ideal factor uniquely and naturally through its
actual quotient. This is a bounded algebraic step for local deformation
conditions; no arithmetic condition is asserted to be cut out by such an ideal.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace Deformation.ProartinianCat

universe u
variable {O : Type u} [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  (U : ProartinianCat O) (I : OpenIdeal U)

/-- The condition that a parameter morphism kills the chosen open ideal. -/
def KillsOpenIdeal {A : ProartinianCat O} (f : U ⟶ A) : Prop :=
  OpenIdeal.ideal I ≤ RingHom.ker f.hom.toRingHom

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- Killing an ideal is preserved by further change of coefficients. -/
theorem killsOpenIdeal_comp {A B : ProartinianCat O} (f : U ⟶ A) (g : A ⟶ B)
    (hf : KillsOpenIdeal U I f) : KillsOpenIdeal U I (f ≫ g) := by
  intro x hx
  change g.hom (f.hom x) = 0
  rw [show f.hom x = 0 from hf hx, map_zero]

/-- Construct the factor using the algebra quotient and its discrete topology. -/
def factorOpenIdeal {A : ProartinianCat O} (f : U ⟶ A)
    (hf : KillsOpenIdeal U I f) : openIdealQuotient U I ⟶ A where
  hom := by
    change (U ⧸ OpenIdeal.ideal I) →A[O] A
    let : DiscreteTopology (U ⧸ OpenIdeal.ideal I) :=
      QuotientAddGroup.discreteTopology (OpenIdeal.isOpen I)
    exact
      { toAlgHom := Ideal.Quotient.liftₐ (OpenIdeal.ideal I) f.hom.toAlgHom hf
        cont := continuous_of_discreteTopology }

/-- The constructed factor agrees on every original parameter. -/
@[simp] theorem factorOpenIdeal_mk {A : ProartinianCat O} (f : U ⟶ A)
    (hf : KillsOpenIdeal U I f) (x : U) :
    (factorOpenIdeal U I f hf).hom (Ideal.Quotient.mk (OpenIdeal.ideal I) x) =
      f.hom x := rfl

/-- The factor has the required composite with the quotient projection. -/
@[simp] theorem quotient_comp_factorOpenIdeal {A : ProartinianCat O} (f : U ⟶ A)
    (hf : KillsOpenIdeal U I f) :
    openIdealQuotientHom U I ≫ factorOpenIdeal U I f hf = f := by
  apply hom_ext
  ext x
  rfl

/-- Surjectivity of the actual quotient projection proves uniqueness. -/
theorem factorOpenIdeal_unique {A : ProartinianCat O} (f : U ⟶ A)
    (hf : KillsOpenIdeal U I f) (g : openIdealQuotient U I ⟶ A)
    (hg : openIdealQuotientHom U I ≫ g = f) : g = factorOpenIdeal U I f hf := by
  apply hom_ext
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (fun t : U ⟶ A ↦ t.hom y) hg

/-- The universal property is an equivalence, not an input field. -/
def openIdealFactorEquiv (A : ProartinianCat O) :
    (openIdealQuotient U I ⟶ A) ≃ {f : U ⟶ A // KillsOpenIdeal U I f} where
  toFun g := ⟨openIdealQuotientHom U I ≫ g, by
    intro x hx
    change g.hom (Ideal.Quotient.mk (OpenIdeal.ideal I) x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]⟩
  invFun f := factorOpenIdeal U I f.val f.property
  left_inv g := (factorOpenIdeal_unique U I _ _ g rfl).symm
  right_inv f := Subtype.ext (quotient_comp_factorOpenIdeal U I f.val f.property)

/-- Factorization is compatible with coefficient morphisms. -/
theorem factorOpenIdeal_natural {A B : ProartinianCat O} (f : U ⟶ A)
    (hf : KillsOpenIdeal U I f) (g : A ⟶ B) :
    factorOpenIdeal U I f hf ≫ g =
      factorOpenIdeal U I (f ≫ g) (killsOpenIdeal_comp U I f g hf) := by
  apply factorOpenIdeal_unique
  rw [← Category.assoc, quotient_comp_factorOpenIdeal]

/-- The subfunctor of parameter maps satisfying this quotient condition. -/
def openIdealCondition : Subfunctor (coyoneda.obj (Opposite.op U)) where
  obj _ := {f | KillsOpenIdeal U I f}
  map g f hf := killsOpenIdeal_comp U I f g hf

/-- The constructed quotient corepresents the actual ideal condition. -/
def openIdealConditionCorepresentableBy :
    (openIdealCondition U I).toFunctor.CorepresentableBy (openIdealQuotient U I) where
  homEquiv := openIdealFactorEquiv U I _
  homEquiv_comp g f := by
    apply Subtype.ext
    change openIdealQuotientHom U I ≫ (f ≫ g) = (openIdealQuotientHom U I ≫ f) ≫ g
    exact (Category.assoc _ _ _).symm

end Deformation.ProartinianCat
