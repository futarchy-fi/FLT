/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStructuralStandardSmoothChart
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Lifting smooth points across a local nilpotent coefficient surjection

A standard-smooth chart at the closed image contains the entire local-base
point. Formal smoothness lifts its actual coordinate map across the prescribed
nilpotent surjection, retaining both reduction and the original base map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace FLT.Mazur.SmoothLocalNilpotentLift

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsLocalRing B] {X : Scheme}

/-- Smooth points over a local ring lift across every nilpotent coefficient surjection. -/
theorem exists_lift (f : X ⟶ Spec (.of R)) [Smooth f]
    (φ : A →ₐ[R] B) (hφ : Function.Surjective φ) (hker : IsNilpotent (RingHom.ker φ.toRingHom))
    (x : Spec (.of B) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ s : Spec (.of A) ⟶ X,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ s = x ∧
        s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  obtain ⟨C, a, j, ha, hj, hy, hf⟩ :=
    AffineStructuralStandardSmoothChart.exists_chart f (x (closedPoint B))
  let _ := hj
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    exact ((specializes_closedPoint w).map x.continuous).mem_open
      j.isOpenEmbedding.isOpen_range hy
  let y := IsOpenImmersion.lift j x hr
  have hyj : y ≫ j = x := IsOpenImmersion.lift_fac j x hr
  obtain ⟨q, hq⟩ := Spec.map_surjective y
  have hqa : q.hom.comp a = algebraMap R B := by
    have he : CommRingCat.ofHom (q.hom.comp a) = CommRingCat.ofHom (algebraMap R B) := by
      apply Spec.map_injective
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
        hq, ← hf, ← Category.assoc, hyj, hx]
    exact congrArg CommRingCat.Hom.hom he
  let _ := a.toAlgebra
  let _ : Algebra.IsStandardSmooth R C := RingHom.isStandardSmooth_algebraMap.mp ha
  let p : C →ₐ[R] B := ⟨q.hom, fun r ↦ DFunLike.congr_fun hqa r⟩
  let u := Algebra.FormallySmooth.liftOfSurjective p φ hφ hker
  refine ⟨Spec.map (CommRingCat.ofHom u.toRingHom) ≫ j, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hu : φ.toRingHom.comp u.toRingHom = q.hom :=
      RingHom.ext (Algebra.FormallySmooth.liftOfSurjective_apply p φ hφ hker)
    rw [hu, CommRingCat.ofHom_hom, hq, hyj]
  · rw [Category.assoc, hf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hu : u.toRingHom.comp a = algebraMap R A := RingHom.ext u.commutes
    rw [hu]

end FLT.Mazur.SmoothLocalNilpotentLift
