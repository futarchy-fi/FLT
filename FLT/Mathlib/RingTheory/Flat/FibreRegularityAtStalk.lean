/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.StalkFibreQuotient
public import FLT.Mathlib.RingTheory.Flat.ResiduePresentationPoint
public import Mathlib.RingTheory.Regular.RegularSequence

/-! # Transfer specified fibre equations to the residue fibre of a stalk -/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct RingTheory.Sequence

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-- Ring equivalences preserve weak regularity of the specified ordered list. -/
theorem RingEquiv.isWeaklyRegular_list_map {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* T) (rs : List S) :
    IsWeaklyRegular S rs ↔ IsWeaklyRegular T (rs.map e) :=
  e.toAddEquiv.isWeaklyRegular_congr (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun x _ y ↦ e.map_mul x y))

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The fibre point above an original prime identifies its given equations
with those in the residue fibre of the corresponding map on local rings. -/
theorem weaklyRegular_stalkFibre_of_fibre (P : Ideal S) [P.IsPrime] (rs : List S)
    (q : Ideal ((P.comap (algebraMap R S)).Fiber S)) [q.IsPrime]
    (hq : q.comap includeRight = P)
    (hrs : IsWeaklyRegular (Localization.AtPrime q)
      ((rs.map (includeRight : S →ₐ[R] (P.comap (algebraMap R S)).Fiber S)).map
        (algebraMap _ (Localization.AtPrime q)))) :
    IsWeaklyRegular
      (Localization.AtPrime P ⊗[Localization.AtPrime (P.comap (algebraMap R S))]
        (Localization.AtPrime (P.comap (algebraMap R S)) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime (P.comap (algebraMap R S)))))
      (rs.map (algebraMap S (Localization.AtPrime P))) := by
  let p := P.comap (algebraMap R S)
  let Sp := Localization.AtPrime P
  let T := Sp ⧸ p.map (algebraMap R Sp)
  let e := Fiber.localizedQuotientEquivOfEq p q P hq
  have hrT := (e.toRingEquiv.isWeaklyRegular_list_map _).mp hrs
  have he : (((rs.map (includeRight : S →ₐ[R] p.Fiber S)).map
      (algebraMap _ (Localization.AtPrime q))).map e) =
        (rs.map (algebraMap S Sp)).map (algebraMap Sp T) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro s _
    exact Fiber.localizedQuotientEquivOfEq_algebraMap_one_tmul p q P hq s
  change IsWeaklyRegular T (((rs.map (includeRight : S →ₐ[R] p.Fiber S)).map
    (algebraMap _ (Localization.AtPrime q))).map e) at hrT
  rw [he] at hrT
  have hrT' : IsWeaklyRegular T (rs.map (algebraMap S Sp)) :=
    (isWeaklyRegular_map_algebraMap_iff T T _).mp hrT
  exact ((P.stalkFibreQuotientEquiv (R := R)).toLinearEquiv.isWeaklyRegular_congr _).mpr hrT'

end Ideal
