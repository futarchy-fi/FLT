/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicCocone

/-!
# Affine-target descent for the two pinching charts

The actual equalizer rings give unique descent into any affine target scheme.
This is a prerequisite for arbitrary-target descent, not a scheme pushout claim.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace FLT.Mazur.PinchingAffineDescent

open PolygonNodeEqualizer PolygonNodePresentation PolygonCyclicAtlas

variable (K : Type u) [Field K]

/-- The normalization of the affine one-gon chart. -/
def oneBranch : ProjectiveLine.chart K ⟶ Spec (.of (B (R := K))) :=
  Spec.map (CommRingCat.ofHom (B (R := K)).val.toRingHom)

/-- The other endpoint of the affine one-gon normalization. -/
def chartOne : Spec (.of K) ⟶ ProjectiveLine.chart K :=
  Spec.map (CommRingCat.ofHom (evalRingHom 1))

variable {S : Type u} [CommRing S]

/-- The node ring pullback for ring maps, without assuming maps preserve K. -/
def nodeLift (f g : S →+* K[X])
    (w : (evalRingHom 0).comp f = (evalRingHom 0).comp g) : S →+* A (R := K) :=
  (f.prod g).codRestrict (A (R := K)) (fun s ↦ RingHom.congr_fun w s)

/-- The one-gon equalizer lift for ring maps, without assuming maps preserve K. -/
def oneGonLift (f : S →+* K[X])
    (w : (evalRingHom 0).comp f = (evalRingHom 1).comp f) : S →+* B (R := K) :=
  f.codRestrict (B (R := K)) (fun s ↦ RingHom.congr_fun w s)

/-- Affine targets admit unique descent from the two branches. -/
theorem node_desc_spec {R : CommRingCat.{u}}
    (f g : ProjectiveLine.chart K ⟶ Spec R)
    (w : ProjectiveLine.chartZero K ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃! d : PolygonNodeBranches.node K ⟶ Spec R,
      firstBranch K ≫ d = f ∧ secondBranch K ≫ d = g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have hw : (evalRingHom 0).comp φ.hom = (evalRingHom 0).comp ψ.hom := by
    rw [ProjectiveLine.chartZero, ← Spec.map_comp, ← Spec.map_comp] at w
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  let d := Spec.map (CommRingCat.ofHom (nodeLift K φ.hom ψ.hom hw))
  have hd₁ : firstBranch K ≫ d = Spec.map φ := by
    rw [firstBranch, ← Spec.map_comp]
    rfl
  have hd₂ : secondBranch K ≫ d = Spec.map ψ := by
    rw [secondBranch, ← Spec.map_comp]
    rfl
  refine ⟨d, ⟨hd₁, hd₂⟩, ?_⟩
  rintro e ⟨he₁, he₂⟩
  obtain ⟨ε, rfl⟩ := Spec.map_surjective e
  rw [firstBranch, ← Spec.map_comp] at he₁
  rw [secondBranch, ← Spec.map_comp] at he₂
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun k ↦ k.hom s) (Spec.map_injective he₁))
    (congrArg (fun k ↦ k.hom s) (Spec.map_injective he₂))

/-- Affine targets admit unique descent from the one-gon normalization. -/
theorem oneGon_desc_spec {R : CommRingCat.{u}}
    (f : ProjectiveLine.chart K ⟶ Spec R)
    (w : ProjectiveLine.chartZero K ≫ f = chartOne K ≫ f) :
    ∃! d : Spec (.of (B (R := K))) ⟶ Spec R, oneBranch K ≫ d = f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hw : (evalRingHom 0).comp φ.hom = (evalRingHom 1).comp φ.hom := by
    rw [ProjectiveLine.chartZero, chartOne, ← Spec.map_comp, ← Spec.map_comp] at w
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  let d := Spec.map (CommRingCat.ofHom (oneGonLift K φ.hom hw))
  have hd : oneBranch K ≫ d = Spec.map φ := by
    rw [oneBranch, ← Spec.map_comp]
    rfl
  refine ⟨d, hd, ?_⟩
  intro e he
  obtain ⟨ε, rfl⟩ := Spec.map_surjective e
  rw [oneBranch, ← Spec.map_comp] at he
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply Subtype.ext
  exact congrArg (fun k ↦ k.hom s) (Spec.map_injective he)

/-- The node descent statement for every affine scheme, not only a chosen spectrum. -/
theorem node_desc_affine {Y : Scheme.{u}} [IsAffine Y]
    (f g : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃! d : PolygonNodeBranches.node K ⟶ Y,
      firstBranch K ≫ d = f ∧ secondBranch K ≫ d = g := by
  obtain ⟨d, ⟨hd₁, hd₂⟩, hu⟩ := node_desc_spec K (f ≫ Y.isoSpec.hom) (g ≫ Y.isoSpec.hom)
    (by simpa only [← Category.assoc] using congrArg (fun t ↦ t ≫ Y.isoSpec.hom) w)
  refine ⟨d ≫ Y.isoSpec.inv, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, hd₁, Category.assoc, Y.isoSpec.hom_inv_id, Category.comp_id]
  · rw [← Category.assoc, hd₂, Category.assoc, Y.isoSpec.hom_inv_id, Category.comp_id]
  · rintro e ⟨he₁, he₂⟩
    apply (cancel_mono Y.isoSpec.hom).mp
    simpa using hu (e ≫ Y.isoSpec.hom) ⟨by rw [← Category.assoc, he₁],
      by rw [← Category.assoc, he₂]⟩

/-- One-gon descent for every affine target scheme. -/
theorem oneGon_desc_affine {Y : Scheme.{u}} [IsAffine Y]
    (f : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = chartOne K ≫ f) :
    ∃! d : Spec (.of (B (R := K))) ⟶ Y, oneBranch K ≫ d = f := by
  obtain ⟨d, hd, hu⟩ := oneGon_desc_spec K (f ≫ Y.isoSpec.hom)
    (by simpa only [← Category.assoc] using congrArg (fun t ↦ t ≫ Y.isoSpec.hom) w)
  refine ⟨d ≫ Y.isoSpec.inv, ?_, ?_⟩
  · dsimp only
    rw [← Category.assoc, hd, Category.assoc, Y.isoSpec.hom_inv_id, Category.comp_id]
  · intro e he
    apply (cancel_mono Y.isoSpec.hom).mp
    simpa using hu (e ≫ Y.isoSpec.hom) (by dsimp only; rw [← Category.assoc, he])

end FLT.Mazur.PinchingAffineDescent
