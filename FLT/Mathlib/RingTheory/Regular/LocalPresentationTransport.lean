/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.UnitMultiples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-! # Transport local regular relations through a coordinate algebra equivalence -/

@[expose] public noncomputable section

/-- A ring equivalence preserves regularity of a relation list in its given order. -/
theorem RingEquiv.isRegular_list_map {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* T) (rs : List S) :
    RingTheory.Sequence.IsRegular S rs ↔ RingTheory.Sequence.IsRegular T (rs.map e) :=
  e.toAddEquiv.isRegular_congr (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun x _ y ↦ e.map_mul x y))

namespace AlgEquiv

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- The local coordinate equivalence sends extended ideals to extended ideals. -/
theorem map_localized_ideal (e : S ≃ₐ[R] T) (Q : Ideal T) [Q.IsPrime] (I : Ideal S) :
    (I.map (algebraMap S (Localization.AtPrime (Q.comap e)))).map
      (Localization.localAlgEquiv _ Q e rfl).toRingHom =
    (I.map e.toRingHom).map (algebraMap T (Localization.AtPrime Q)) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro s
  exact Localization.localRingHom_to_map _ _ _ rfl s

/-- Regular relations and their length survive a change of local coordinates. -/
theorem exists_local_regular_relations_of_equiv (e : S ≃ₐ[R] T)
    (Q : Ideal T) [Q.IsPrime] (I : Ideal S)
    (rs : List (Localization.AtPrime (Q.comap e)))
    (hgen : Ideal.ofList rs = I.map (algebraMap S _))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime (Q.comap e)) rs) :
    ∃ ts : List (Localization.AtPrime Q), ts.length = rs.length ∧
      Ideal.ofList ts = (I.map e.toRingHom).map (algebraMap T _) ∧
      RingTheory.Sequence.IsRegular (Localization.AtPrime Q) ts := by
  let e' := Localization.localAlgEquiv _ Q e rfl
  refine ⟨rs.map e', List.length_map .., ?_, ?_⟩
  · change Ideal.ofList (rs.map e'.toRingHom) = _
    rw [← Ideal.map_ofList, hgen]
    exact e.map_localized_ideal Q I
  · exact (e'.toRingEquiv.isRegular_list_map rs).mp hreg

end AlgEquiv
