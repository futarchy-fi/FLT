/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The exact quotient square is a pushout

Extending an ideal and then quotienting constructs the scalar extension of
the original quotient. The universal property keeps the full ideal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.ScalarQuotientPushout
variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (I : Ideal R)

/-- The induced map between the original quotient and its extended quotient. -/
def map : R ⧸ I →+* S ⧸ I.map φ :=
  Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map

/-- The quotient map retains the original scalar coordinate. -/
theorem map_mk (r : R) :
    map φ I (Ideal.Quotient.mk I r) = Ideal.Quotient.mk (I.map φ) (φ r) := rfl

/-- The full extended ideal gives the actual categorical scalar pushout. -/
theorem isPushout : IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I))
    (CommRingCat.ofHom φ) (CommRingCat.ofHom (map φ I))
    (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))) := by
  have hw : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom (map φ I) =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ)) := rfl
  refine ⟨⟨hw⟩, ⟨PushoutCocone.isColimitAux' (PushoutCocone.mk _ _ hw) ?_⟩⟩
  intro c
  have hc (r : R) : c.inl (Ideal.Quotient.mk I r) = c.inr (φ r) :=
    congrArg (fun f : CommRingCat.of R ⟶ c.pt ↦ f r) c.condition
  have hker : I.map φ ≤ RingHom.ker c.inr.hom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change c.inr (φ r) = 0
    rw [← hc, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  let d := CommRingCat.ofHom (Ideal.Quotient.lift (I.map φ) c.inr.hom hker)
  refine ⟨d, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact (hc r).symm
  · rfl
  · intro m _ hm
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact congrArg (fun f : CommRingCat.of S ⟶ c.pt ↦ f s) hm

end FLT.Mazur.ScalarQuotientPushout
