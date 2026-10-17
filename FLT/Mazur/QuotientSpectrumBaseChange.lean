/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Original quotient spectra under arbitrary affine base change

The ring quotient by the mapped ideal is the actual Cartesian restriction.
The proof uses the quotient universal property and does not expand tensors.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.QuotientSpectrumBaseChange
universe u
variable {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B) (I : Ideal A)

/-- The original map on the two quotient coordinate rings. -/
def map : A ⧸ I →+* B ⧸ I.map ρ :=
  Ideal.quotientMap (I.map ρ) ρ Ideal.le_comap_map

/-- The quotient square retains its original scalar maps. -/
theorem condition :
    (Ideal.Quotient.mk (I.map ρ)).comp ρ = (map ρ I).comp (Ideal.Quotient.mk I) := by
  ext x
  rfl

/-- Compatible maps annihilate the entire mapped ideal. -/
theorem ker_le (s : PushoutCocone (CommRingCat.ofHom ρ)
    (CommRingCat.ofHom (Ideal.Quotient.mk I))) : I.map ρ ≤ RingHom.ker s.inl.hom := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change s.inl.hom (ρ x) = 0
  have hw := congrArg (fun k ↦ k.hom x) s.condition
  change s.inl.hom (ρ x) = s.inr.hom (Ideal.Quotient.mk I x) at hw
  rw [hw, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- The universal descended coordinate map from the original quotient. -/
def desc (s : PushoutCocone (CommRingCat.ofHom ρ)
    (CommRingCat.ofHom (Ideal.Quotient.mk I))) : CommRingCat.of (B ⧸ I.map ρ) ⟶ s.pt :=
  CommRingCat.ofHom (Ideal.Quotient.lift (I.map ρ) s.inl.hom (ker_le ρ I s))

/-- Quotient by the mapped ideal is the full pushout, with no flatness assumption. -/
theorem isPushout : IsPushout (CommRingCat.ofHom ρ)
    (CommRingCat.ofHom (Ideal.Quotient.mk I))
    (CommRingCat.ofHom (Ideal.Quotient.mk (I.map ρ))) (CommRingCat.ofHom (map ρ I)) := by
  have hw : CommRingCat.ofHom ρ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.map ρ)) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom (map ρ I) :=
    CommRingCat.hom_ext (condition ρ I)
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw)
    (PushoutCocone.IsColimit.mk _ (desc ρ I) ?_ ?_ ?_)
  · intro s
    rfl
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun k ↦ k.hom a) s.condition
  · intro s k hk _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun k ↦ k.hom b) hk

/-- The exact original quotient spectrum is the affine base change of the original quotient. -/
theorem isPullback : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map ρ))))
    (Spec.map (CommRingCat.ofHom (map ρ I)))
    (Spec.map (CommRingCat.ofHom ρ))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout ρ I)

/-- The same Cartesian square expressed with an equal original target ideal. -/
theorem isPullback_of_map_eq (J : Ideal B) (hIJ : I.map ρ = J) : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J ρ
      (Ideal.map_le_iff_le_comap.mp hIJ.le))))
    (Spec.map (CommRingCat.ofHom ρ))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  subst J
  exact isPullback ρ I

/-- The original scalar map at any power of the parameter ideal. -/
def powerMap (m : ℕ) : A ⧸ I ^ m →+* B ⧸ (I.map ρ) ^ m :=
  Ideal.quotientMap ((I.map ρ) ^ m) ρ (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])

/-- The power quotient is exactly the original finite-order affine restriction. -/
theorem power_isPullback (m : ℕ) : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I.map ρ) ^ m))))
    (Spec.map (CommRingCat.ofHom (powerMap ρ I m)))
    (Spec.map (CommRingCat.ofHom ρ))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ m)))) := by
  exact isPullback_of_map_eq ρ (I ^ m) ((I.map ρ) ^ m) (Ideal.map_pow ρ I m)

end FLT.Mazur.QuotientSpectrumBaseChange
