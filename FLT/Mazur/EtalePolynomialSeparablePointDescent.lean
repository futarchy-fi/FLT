/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleSepClosedPointDescent
public import FLT.Mazur.SeparableAffineCoordinates
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Whole-point descent from separable étale coordinates

In an étale polynomial chart over a field, separability of the polynomial
coordinates forces the whole geometric point to descend to the relative
separable closure. This retains the original point, not only its coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EtalePolynomialSeparablePointDescent
set_option backward.isDefEq.respectTransparency false
variable {k K B : Type} [Field k] [Field K] [IsSepClosed K] [Algebra k K] [CommRing B]

/-- Separable coordinates descend the original point to the relative separable closure. -/
theorem exists_factor {n : ℕ} (g : MvPolynomial (Fin n) k →+* B) (hg : g.Etale)
    (q : B →+* K) (hq : q.comp (g.comp MvPolynomial.C) = algebraMap k K)
    (hs : ∀ i, IsSeparable k (q (g (MvPolynomial.X i)))) :
    ∃ q₀ : B →+* separableClosure k K,
      (algebraMap (separableClosure k K) K).comp q₀ = q := by
  let _ : IsSepClosed (separableClosure k K) := IsSepClosure.sep_closed k
  let a (i : Fin n) : separableClosure k K := ⟨q (g (MvPolynomial.X i)), hs i⟩
  let t := MvPolynomial.eval₂Hom (algebraMap k (separableClosure k K)) a
  have he : q.comp g = (algebraMap (separableClosure k K) K).comp t := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, t, MvPolynomial.eval₂Hom_C,
        ← IsScalarTower.algebraMap_apply] using RingHom.congr_fun hq r
    · intro i
      simp only [RingHom.comp_apply, t, MvPolynomial.eval₂Hom_X']
      rfl
  let G := Spec.map (CommRingCat.ofHom g)
  let _ : Etale G := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  have hp : Spec.map (CommRingCat.ofHom q) ≫ G =
      Spec.map (CommRingCat.ofHom (algebraMap (separableClosure k K) K)) ≫
        Spec.map (CommRingCat.ofHom t) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) he
  obtain ⟨y, _, hy⟩ := EtaleSepClosedPointDescent.exists_factor G
    (Spec.map (CommRingCat.ofHom t)) (algebraMap (separableClosure k K) K)
    (Spec.map (CommRingCat.ofHom q)) hp
  obtain ⟨q₀, hq₀⟩ := Spec.map_surjective y
  refine ⟨q₀.hom, ?_⟩
  rw [← hq₀, ← Spec.map_comp] at hy
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hy)

end FLT.Mazur.EtalePolynomialSeparablePointDescent
