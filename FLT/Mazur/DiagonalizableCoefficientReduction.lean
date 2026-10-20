/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableInfinitesimalIdeal

/-!
# Actual quotient-base reduction of character coordinates

The surjective map reduces coefficients to the specified quotient ring and
retains every character. Its kernel is the complete infinitesimal ideal used
in smooth-group deformation, with no abstract replacement of the target.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DiagonalizableCobar

variable (R G : Type*) [CommRing R] [AddCommMonoid G] (I : Ideal R)

/-- Coefficient reduction as an algebra map over the original base. -/
def coefficientReduction : AddMonoidAlgebra R G →ₐ[R] AddMonoidAlgebra (R ⧸ I) G where
  __ := AddMonoidAlgebra.mapRingHom G (Ideal.Quotient.mk I)
  commutes' r := by simp

/-- Each full original character retains its original quotient coefficient. -/
theorem coefficientReduction_single (a : G) (r : R) :
    coefficientReduction R G I (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single a (Ideal.Quotient.mk I r) := by
  simp [coefficientReduction]

/-- Every function on the quotient-base diagonalizable scheme has an actual lift. -/
theorem coefficientReduction_surjective : Function.Surjective (coefficientReduction R G I) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add p q hp hq =>
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    exact ⟨x + y, map_add _ _ _⟩
  | single a r =>
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ⟨AddMonoidAlgebra.single a s, coefficientReduction_single R G I a s⟩

/-- The actual reduction has the entire coefficient ideal as its kernel. -/
theorem coefficientReduction_ker :
    RingHom.ker (coefficientReduction R G I).toRingHom = coefficientIdeal R G I := rfl

/-- Coefficient reduction commutes with every full character substitution. -/
theorem coefficientReduction_mapDomain {H : Type*} [AddCommMonoid H] (f : G →+ H)
    (p : AddMonoidAlgebra R G) :
    coefficientReduction R H I (AddMonoidAlgebra.mapDomainAlgHom R R f p) =
      AddMonoidAlgebra.mapDomainAlgHom R (R ⧸ I) f (coefficientReduction R G I p) := by
  exact DFunLike.congr_fun
    (AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom (Ideal.Quotient.mk I) f) p

/-- The constructed correction commutes with any change of coefficient ring. -/
theorem correction_map {S : Type*} [CommRing S] (f : R →+* S)
    (p : AddMonoidAlgebra R (G × G)) :
    correction S G (AddMonoidAlgebra.mapRingHom (G × G) f p) =
      AddMonoidAlgebra.mapRingHom G f (correction R G p) := by
  ext a
  rfl

end FLT.Mazur.DiagonalizableCobar
