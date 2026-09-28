/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFlatQuotient
public import FLT.GroupScheme.RaynaudRankThreeExtension
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Unramified.Finite

/-!
# Faithful flatness over unramified quotient coordinates

A finite flat algebra is faithfully flat over an unramified finite subalgebra.
Applied to contracted generic quotients, this supplies genuine faithful flatness
when the integral quotient is unramified. The ramified case is not asserted.
-/

@[expose] public noncomputable section

namespace Subalgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A finite flat algebra is faithfully flat over any finite unramified subalgebra. -/
theorem faithfullyFlat_of_formallyUnramified (D : Subalgebra R A)
    [Module.Finite R A] [Module.Flat R A] [Module.Finite R D]
    [Algebra.FormallyUnramified R D] : Module.FaithfullyFlat D A := by
  let : Module.Flat D A := Algebra.FormallyUnramified.flat_of_restrictScalars R D A
  let : Module.Finite D A := Module.Finite.of_restrictScalars_finite R D A
  exact Module.FaithfullyFlat.of_comap_surjective (Algebra.IsIntegral.comap_surjective D A)

end Subalgebra

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R]
    {X Y : FF R K}

/-- The projection to a contracted unramified quotient is faithfully flat on
coordinate rings, without any splitting hypothesis on its generic point group. -/
theorem GenericGaloisHom.quotientCoordinates_faithfullyFlat_of_formallyUnramified
    (q : GenericGaloisHom X Y)
    [Algebra.FormallyUnramified R q.quotientCoordinates] :
    Module.FaithfullyFlat q.quotientCoordinates X.CoordinateRing :=
  q.quotientCoordinates.faithfullyFlat_of_formallyUnramified

/-- If a three-adic generic quotient has an unramified order-three model,
its contracted integral quotient is unramified as well. -/
theorem GenericGaloisHom.quotientCoordinates_formallyUnramified_of_order_three
    {X Y : FF ℤ_[3] ℚ_[3]} (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) (hY : Nat.card Y.Points = 3)
    [Algebra.FormallyUnramified ℤ_[3] Y.CoordinateRing] :
    Algebra.FormallyUnramified ℤ_[3] q.quotientCoordinates := by
  let Q := q.flatQuotient hq
  let e : GenericGaloisHom Q Y :=
    { toFun := id
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  obtain ⟨g, hg, _⟩ := raynaud_extend_generic_morphism_of_order_three Q Y hY e
  have hi : Function.Injective g := by
    apply ModelHom.injective_of_baseChange_injective
    rw [← ModelHom.toBialgHom_genericHom, hg]
    exact e.toBialgHom_injective Function.surjective_id
  have hs := raynaud_integral_rigidity_of_order_three Y Q hY hY g hi
  exact Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofBijective g.toAlgHom ⟨hi, hs⟩)

/-- Every generic surjection onto an unramified order-three model gives a
faithfully flat contracted quotient, including for nonsplit extensions. -/
theorem GenericGaloisHom.quotientCoordinates_faithfullyFlat_of_unramified_order_three
    {X Y : FF ℤ_[3] ℚ_[3]} (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) (hY : Nat.card Y.Points = 3)
    [Algebra.FormallyUnramified ℤ_[3] Y.CoordinateRing] :
    Module.FaithfullyFlat q.quotientCoordinates X.CoordinateRing := by
  let := q.quotientCoordinates_formallyUnramified_of_order_three hq hY
  exact q.quotientCoordinates_faithfullyFlat_of_formallyUnramified

end ThreeAdicPlan
