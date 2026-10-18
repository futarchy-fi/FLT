/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormallySmoothResidueLift
public import FLT.Mazur.AffineStructuralStandardSmoothChart

/-!
# Smooth rational points lift over the original complete local base

A standard smooth affine neighborhood of the prescribed residue point supplies
the coordinate algebra. Its constructed complete lift gives an actual section
of the original scheme, retaining the specified point and coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SmoothCompleteResidueLift
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] {X : Scheme}

/-- Every rational point of a smooth scheme extends over a complete quotient base. -/
theorem exists_lift (f : X ⟶ Spec (.of R)) [Smooth f]
    (φ : R →+* K) (hφ : Function.Surjective φ)
    [IsAdicComplete (RingHom.ker φ) R] (x : Spec (.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom φ)) :
    ∃ s : Spec (.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom φ) ≫ s = x ∧ s ≫ f = 𝟙 _ := by
  obtain ⟨A, a, j, ha, hj, hy, hf⟩ :=
    AffineStructuralStandardSmoothChart.exists_chart f (x (IsLocalRing.closedPoint K))
  let _ := hj
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    simpa only [Subsingleton.elim w (IsLocalRing.closedPoint K)] using hy
  let y := IsOpenImmersion.lift j x hr
  have hyj : y ≫ j = x := IsOpenImmersion.lift_fac j x hr
  obtain ⟨q, hq⟩ := Spec.map_surjective y
  have hqa : q.hom.comp a = φ := by
    have he : CommRingCat.ofHom (q.hom.comp a) = CommRingCat.ofHom φ := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
        hq, ← hf, ← Category.assoc, hyj, hx]
    exact congrArg CommRingCat.Hom.hom he
  let _ := a.toAlgebra
  let _ := φ.toAlgebra
  let _ : Algebra.IsStandardSmooth R A := RingHom.isStandardSmooth_algebraMap.mp ha
  let p : A →ₐ[R] K := ⟨q.hom, fun r ↦ DFunLike.congr_fun hqa r⟩
  let u := AdicFormallySmoothResidueLift.lift hφ p
  let s := Spec.map (CommRingCat.ofHom u.toRingHom) ≫ j
  refine ⟨s, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom u.toRingHom) ≫ j = x
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hu : φ.comp u.toRingHom = q.hom :=
      RingHom.ext (AdicFormallySmoothResidueLift.reduction_lift hφ p)
    rw [hu, CommRingCat.ofHom_hom, hq, hyj]
  · change (Spec.map (CommRingCat.ofHom u.toRingHom) ≫ j) ≫ f = 𝟙 _
    rw [Category.assoc, hf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hu : u.toRingHom.comp a = RingHom.id R := RingHom.ext u.commutes
    rw [hu, CommRingCat.ofHom_id, Spec.map_id]

end FLT.Mazur.SmoothCompleteResidueLift
