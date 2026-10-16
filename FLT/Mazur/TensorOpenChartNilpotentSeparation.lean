/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChartVanishingSeparation

/-!
# Nilpotent base parameters separate full original tensor charts

An original intersection away from a parameter stays empty after coefficient
extension making that parameter nilpotent, at every arithmetic thickening.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.TensorOpenChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] {X U : Scheme.{u}}
  (base : X ⟶ Spec (.of R)) (i : U ⟶ X) (j : Spec (.of A) ⟶ X)
  (hj : j ≫ base = Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (π : R) (hπ : IsNilpotent (algebraMap R S π))
  (h : ∀ (a : U) (c : Spec (.of A)), i a = j c → π ∉ (base (j c)).asIdeal)
local notation "p" => pullback.snd
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) base
local notation "old" => pullback.snd i p
local notation "new" => chart (S := S) base j hj

include hπ h in
/-- Nilpotent coefficient extension separates the entire original chart images. -/
theorem nilpotent_disjoint : Disjoint (Set.range old) (Set.range new) := by
  obtain ⟨k, hk⟩ := hπ
  apply vanishing_disjoint base i j hj (π ^ k) (by rw [map_pow, hk])
  intro a c he hp
  exact h a c he ((base (j c)).isPrime.mem_of_pow_mem k hp)

include hπ h in
/-- The full scheme-theoretic intersection is empty at every nilpotent coefficient order. -/
theorem nilpotent_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) old new := by
  let _ := Scheme.isEmpty_pullback old new (nilpotent_disjoint base i j hj π hπ h)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback old new)))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.TensorOpenChart
