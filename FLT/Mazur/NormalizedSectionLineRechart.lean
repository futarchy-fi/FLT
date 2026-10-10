/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineOverlapBaseChange

/-!
# Constructing a new coordinate chart of a section line

A coordinate of the normalized generator that is a unit gives another
trivialization of the same submodule. This constructs the overlap rather
than assuming a second chart, and computes its generator and transition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.NormalizedSectionLine
variable {R S : Type u} [CommRing R] [CommRing S] {ι : Type u}

/-- A unit coordinate makes its projection an isomorphism on the original submodule. -/
def rechart (i j : ι) (L : Chart R ι i) (a : Rˣ)
    (ha : generator R ι i L j = a) : Chart R ι j := by
  refine ⟨L.val, ?_⟩
  let e := (trivialization R ι i L).trans (LinearEquiv.smulOfUnit a : R ≃ₗ[R] R)
  have he : (coordinate R ι j L.val : L.val → R) = e := by
    funext v
    have h := congrFun (eq_smul_generator R ι i L v) j
    change v.val j = (a : R) * v.val i
    simpa only [Pi.smul_apply, smul_eq_mul, ha, mul_comm] using h
  rw [he]
  exact e.bijective

/-- Recharting retains the actual submodule, hence the same ambient sheaf inclusion. -/
lemma rechart_val (i j : ι) (L : Chart R ι i) (a : Rˣ)
    (ha : generator R ι i L j = a) : (rechart i j L a ha).val = L.val := rfl

/-- The original generator is rescaled by the inverse unit in the new chart. -/
lemma generator_rechart (i j : ι) (L : Chart R ι i) (a : Rˣ)
    (ha : generator R ι i L j = a) :
    generator R ι j (rechart i j L a ha) = (↑a⁻¹ : R) • generator R ι i L := by
  have h := generator_change R ι i j L (rechart i j L a ha) rfl
  rw [ha] at h
  rw [h, smul_smul, Units.inv_mul, one_smul]

/-- The constructed overlap has exactly the specified unit as its transition. -/
lemma transitionUnit_rechart (i j : ι) (L : Chart R ι i) (a : Rˣ)
    (ha : generator R ι i L j = a) :
    transitionUnit R ι i j L (rechart i j L a ha) rfl = a :=
  Units.ext ha

/-- Recharting commutes with every coefficient extension as an actual line submodule. -/
lemma baseChange_rechart (φ : R →+* S) (i j : ι) (L : Chart R ι i) (a : Rˣ)
    (ha : generator R ι i L j = a) :
    baseChange φ j (rechart i j L a ha) =
      rechart i j (baseChange φ i L) (Units.map φ.toMonoidHom a)
        (by rw [generator_baseChange]; exact congrArg φ ha) := by
  apply Subtype.ext
  exact baseChange_val_eq φ j i (rechart i j L a ha) L rfl

end FLT.Mazur.NormalizedSectionLine
