/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineLinearTransport

/-!
# Coordinate transport commutes with arbitrary coefficient extension

A genuine coefficient square of ambient linear equivalences carries the
same actual section submodule along either route. The target chart and its
unit coordinate are constructed from the original generator and ring map.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.NormalizedSectionLine
variable {R S : Type u} [CommRing R] [CommRing S] {ι κ : Type u}
variable (φ : R →+* S) (e : (ι → R) ≃ₗ[R] (κ → R)) (d : (ι → S) ≃ₗ[S] (κ → S))
variable (h : ∀ v, (fun k ↦ φ (e v k)) = d (fun k ↦ φ (v k)))
include h

/-- The transported coordinate remains the image of its original unit after coefficient change. -/
lemma linearTransport_baseChange_unit (i : ι) (j : κ) (L : Chart R ι i)
    (a : Rˣ) (ha : e (generator R ι i L) j = a) :
    d (generator S ι i (baseChange φ i L)) j = (Units.map φ.toMonoidHom a : S) := by
  rw [generator_baseChange, ← h]
  exact congrArg φ ha

/-- Ambient coordinate transport commutes with extension of the actual line submodule. -/
lemma linearTransport_baseChange (i : ι) (j : κ) (L : Chart R ι i)
    (a : Rˣ) (ha : e (generator R ι i L) j = a) :
    baseChange φ j (linearTransport e i j L a ha) =
      linearTransport d i j (baseChange φ i L) (Units.map φ.toMonoidHom a)
        (linearTransport_baseChange_unit φ e d h i j L a ha) := by
  apply (tupleEquiv S κ j).symm.injective
  apply Subtype.ext
  funext k
  change generator S κ j _ k = generator S κ j _ k
  simp only [generator_baseChange, generator_linearTransport, Pi.smul_apply, smul_eq_mul]
  rw [map_mul, ← h]
  rfl

end FLT.Mazur.NormalizedSectionLine
