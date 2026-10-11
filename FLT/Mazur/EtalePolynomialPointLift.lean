/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCoordinateSlice
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Étale lifting of polynomial-coordinate points

If the base ring surjects onto a test ring, every point in an étale polynomial
chart lifts to an actual étale base neighborhood. The coordinate section is
constructed by lifting its finitely many values; it is not an input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtalePolynomialPointLift
set_option backward.isDefEq.respectTransparency false
variable {R B K : Type} [CommRing R] [CommRing B] [CommRing K]

/-- Surjectivity on coefficients supplies a matching polynomial-coordinate section. -/
theorem exists_coordinates {n : ℕ} (g : MvPolynomial (Fin n) R →+* B)
    (q : B →+* K) (φ : R →+* K) (hφ : Function.Surjective φ)
    (hq : q.comp (g.comp MvPolynomial.C) = φ) :
    ∃ a : Fin n → R, q.comp g = φ.comp (MvPolynomial.eval₂Hom (RingHom.id R) a) := by
  choose a ha using fun i : Fin n ↦ hφ (q (g (MvPolynomial.X i)))
  refine ⟨a, ?_⟩
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
      using RingHom.congr_fun hq r
  · intro i
    simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X'] using (ha i).symm

/-- A matching test point lifts along a constructed étale neighborhood of the original base. -/
theorem exists_lift {n : ℕ} (g : MvPolynomial (Fin n) R →+* B) (hg : g.Etale)
    (q : B →+* K) (φ : R →+* K) (hφ : Function.Surjective φ)
    (hq : q.comp (g.comp MvPolynomial.C) = φ) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ Spec (.of B))
      (z : Spec (.of K) ⟶ E),
      Etale e ∧ v ≫ Spec.map (CommRingCat.ofHom (g.comp MvPolynomial.C)) = e ∧
        z ≫ e = Spec.map (CommRingCat.ofHom φ) ∧
        z ≫ v = Spec.map (CommRingCat.ofHom q) := by
  obtain ⟨a, ha⟩ := exists_coordinates g q φ hφ hq
  let G := Spec.map (CommRingCat.ofHom g)
  let P := Spec.map
    (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
  let t := Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id R) a))
  have ht : t ≫ P = 𝟙 _ := by
    rw [← Spec.map_id, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact MvPolynomial.eval₂Hom_C _ _ _
  have hG : Etale G := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  let _ := hG
  have hpoint : Spec.map (CommRingCat.ofHom q) ≫ G =
      Spec.map (CommRingCat.ofHom φ) ≫ t := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k)) ha
  refine ⟨EtaleCoordinateSlice.space G t, EtaleCoordinateSlice.toBase G t,
    EtaleCoordinateSlice.toSource G t,
    EtaleCoordinateSlice.pointLift G t _ _ hpoint, inferInstance, ?_,
    EtaleCoordinateSlice.pointLift_base _ _ _ _ _,
    EtaleCoordinateSlice.pointLift_source _ _ _ _ _⟩
  have h := EtaleCoordinateSlice.toSource_base G P t ht
  simpa only [G, P, ← CommRingCat.ofHom_comp, ← Spec.map_comp] using h

end FLT.Mazur.EtalePolynomialPointLift
