/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelDiagramTransport
public import FLT.Mazur.IntegerModelOpenImmersionBaseChange

/-!
# Retaining overlap pullbacks under coefficient enlargement

A cartesian square between four fixed coefficient models stays cartesian
when all its maps are transported. The proof pastes the coefficient base
change squares and cancels one of them; coefficient inclusions need not be flat.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- An established overlap pullback remains a pullback at every larger stage. -/
theorem integerModelTransportHom_preserves_pullback {A B C D E : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra A E]
    {n m r t p q k l : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (R : Algebra.Presentation A D (Fin p) (Fin q))
    (T : Algebra.Presentation A E (Fin k) (Fin l))
    {A₀ A₁ : Subalgebra ℤ A}
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀] [R.HasCoeffs A₀] [T.HasCoeffs A₀]
    [P.HasCoeffs A₁] [Q.HasCoeffs A₁] [R.HasCoeffs A₁] [T.HasCoeffs A₁]
    (h : A₀ ≤ A₁)
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (g : P.ModelOfHasCoeffs A₀ →ₐ[A₀] R.ModelOfHasCoeffs A₀)
    (i : Q.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (j : R.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (hp : IsPullback (Spec.map (CommRingCat.ofHom i.toRingHom))
      (Spec.map (CommRingCat.ofHom j.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (integerModelTransportHom Q T h i).toRingHom))
      (Spec.map (CommRingCat.ofHom (integerModelTransportHom R T h j).toRingHom))
      (Spec.map (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom))
      (Spec.map (CommRingCat.ofHom (integerModelTransportHom P R h g).toRingHom)) := by
  have hAlg : i.comp f = j.comp g := by
    have hh := hp.w
    rw [← Spec.map_comp, ← Spec.map_comp] at hh
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective hh))
  have htrans : (integerModelTransportHom Q T h i).comp
      (integerModelTransportHom P Q h f) =
      (integerModelTransportHom R T h j).comp (integerModelTransportHom P R h g) := by
    rw [← integerModelTransportHom_comp, ← integerModelTransportHom_comp, hAlg]
  have hcomm :
      Spec.map (CommRingCat.ofHom (integerModelTransportHom Q T h i).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom) =
      Spec.map (CommRingCat.ofHom (integerModelTransportHom R T h j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (integerModelTransportHom P R h g).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun a : P.ModelOfHasCoeffs A₁ →ₐ[A₁] T.ModelOfHasCoeffs A₁ ↦
      Spec.map (CommRingCat.ofHom a.toRingHom)) htrans
  have ht := (integerModelTransportHom_isPullback R T h j).paste_horiz hp
  rw [(integerModelTransportHom_isPullback Q T h i).w,
    (integerModelTransportHom_isPullback P R h g).w] at ht
  exact ht.of_right hcomm (integerModelTransportHom_isPullback P Q h f)

end FLT.Mazur.Approximation
