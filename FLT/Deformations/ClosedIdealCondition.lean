/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ClosedIdealQuotient
public import FLT.Deformations.Subfunctor

/-!
# Closed ideal conditions on a proartinian parameter ring

Maps killing a proper closed ideal factor uniquely and naturally through its
actual quotient with its quotient topology. No arithmetic condition is asserted
to be cut out by such an ideal.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace Deformation.ProartinianCat

universe u
variable {O : Type u} [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)]
  (U : ProartinianCat O) (I : Ideal U)
  (hI : IsClosed (I : Set U)) (hne : I ≠ ⊤)

/-- The condition that a parameter morphism kills the chosen ideal. -/
def KillsClosedIdeal {A : ProartinianCat O} (f : U ⟶ A) : Prop :=
  I ≤ RingHom.ker f.hom.toRingHom

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- Killing an ideal is preserved by further change of coefficients. -/
theorem killsClosedIdeal_comp {A B : ProartinianCat O} (f : U ⟶ A) (g : A ⟶ B)
    (hf : KillsClosedIdeal U I f) : KillsClosedIdeal U I (f ≫ g) := by
  intro x hx
  change g.hom (f.hom x) = 0
  rw [show f.hom x = 0 from hf hx, map_zero]

/-- Construct the continuous factor using the quotient topology. -/
def factorClosedIdeal {A : ProartinianCat O} (f : U ⟶ A)
    (hf : KillsClosedIdeal U I f) : closedIdealQuotient U I hI hne ⟶ A where
  hom :=
    { toAlgHom := Ideal.Quotient.liftₐ I f.hom.toAlgHom hf
      cont := ((QuotientRing.isOpenQuotientMap_mk I).isQuotientMap).continuous_iff.mpr f.hom.cont }

/-- The constructed factor agrees on every original parameter. -/
@[simp] theorem factorClosedIdeal_mk {A : ProartinianCat O} (f : U ⟶ A)
    (hf : KillsClosedIdeal U I f) (x : U) :
    (factorClosedIdeal U I hI hne f hf).hom (Ideal.Quotient.mk I x) =
      f.hom x := rfl

/-- The factor has the required composite with the quotient projection. -/
@[simp] theorem quotient_comp_factorClosedIdeal {A : ProartinianCat O} (f : U ⟶ A)
    (hf : KillsClosedIdeal U I f) :
    closedIdealQuotientHom U I hI hne ≫ factorClosedIdeal U I hI hne f hf = f := by
  apply hom_ext
  ext x
  rfl

/-- Surjectivity of the actual quotient projection proves uniqueness. -/
theorem factorClosedIdeal_unique {A : ProartinianCat O} (f : U ⟶ A)
    (hf : KillsClosedIdeal U I f) (g : closedIdealQuotient U I hI hne ⟶ A)
    (hg : closedIdealQuotientHom U I hI hne ≫ g = f) : g = factorClosedIdeal U I hI hne f hf := by
  apply hom_ext
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (fun t : U ⟶ A ↦ t.hom y) hg

/-- The universal property is an equivalence, not an input field. -/
def closedIdealFactorEquiv (A : ProartinianCat O) :
    (closedIdealQuotient U I hI hne ⟶ A) ≃ {f : U ⟶ A // KillsClosedIdeal U I f} where
  toFun g := ⟨closedIdealQuotientHom U I hI hne ≫ g, by
    intro x hx
    change g.hom (Ideal.Quotient.mk I x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]⟩
  invFun f := factorClosedIdeal U I hI hne f.val f.property
  left_inv g := (factorClosedIdeal_unique U I hI hne _ _ g rfl).symm
  right_inv f := Subtype.ext (quotient_comp_factorClosedIdeal U I hI hne f.val f.property)

/-- Factorization is compatible with coefficient morphisms. -/
theorem factorClosedIdeal_natural {A B : ProartinianCat O} (f : U ⟶ A)
    (hf : KillsClosedIdeal U I f) (g : A ⟶ B) :
    factorClosedIdeal U I hI hne f hf ≫ g =
      factorClosedIdeal U I hI hne (f ≫ g) (killsClosedIdeal_comp U I f g hf) := by
  apply factorClosedIdeal_unique
  rw [← Category.assoc, quotient_comp_factorClosedIdeal]

/-- The subfunctor of parameter maps satisfying this quotient condition. -/
def closedIdealCondition : Subfunctor (coyoneda.obj (Opposite.op U)) where
  obj _ := {f | KillsClosedIdeal U I f}
  map g f hf := killsClosedIdeal_comp U I f g hf

/-- The constructed quotient corepresents the actual ideal condition. -/
def closedIdealConditionCorepresentableBy :
    (closedIdealCondition U I).toFunctor.CorepresentableBy (closedIdealQuotient U I hI hne) where
  homEquiv := closedIdealFactorEquiv U I hI hne _
  homEquiv_comp g f := by
    apply Subtype.ext
    change closedIdealQuotientHom U I hI hne ≫ (f ≫ g) = (closedIdealQuotientHom U I hI hne ≫ f) ≫ g
    exact (Category.assoc _ _ _).symm

end Deformation.ProartinianCat
