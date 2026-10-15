/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteFiberGeometricSections
public import FLT.Mazur.EtaleFiniteGeometricAffine
public import FLT.Mazur.UnramifiedSectionImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Spreading every branch of the actual geometric fiber

Enumerate the BASE-CHANGED geometric fiber, including all conjugate residue
branches, before spreading its sections. The resulting open sections cover
the whole fiber over the distinguished point of the new étale neighborhood.
This is stronger than enumerating the original topological fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtaleFiniteGeometricFiberSpread
universe u
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsFinite f]
  {K : Type u} [Field K] [IsSepClosed K] (b : Spec (.of K) ⟶ Y)

/-- Every point of the actual geometric fiber has its own rational section. -/
theorem exists_geometric_sections :
    ∃ (n : ℕ) (s : Fin n → (Spec (.of K) ⟶ pullback f b)),
      (∀ i, s i ≫ pullback.snd f b = 𝟙 _) ∧
      Function.Bijective (fun i ↦ s i default) := by
  let p := pullback.snd f b
  obtain ⟨s, hs, hi, hr⟩ := EtaleFiniteFiberGeometricSections.exists_enumeration p (𝟙 _)
    (p.finite_preimage_singleton default)
  refine ⟨_, s, hs, hi, fun x ↦ ?_⟩
  have hx : x ∈ p ⁻¹' {(𝟙 (Spec (.of K))) default} := Subsingleton.elim _ _
  rw [← hr] at hx
  exact hx

/-- All geometric branches extend to open sections covering the distinguished new fiber. -/
theorem exists_affine_sections :
    ∃ (n : ℕ) (U : Scheme.{u}) (q : U ⟶ Y) (z : Spec (.of K) ⟶ U)
      (s : Fin n → (U ⟶ pullback f q)),
      IsAffine U ∧ Etale q ∧ z ≫ q = b ∧
      (∀ i, s i ≫ pullback.snd f q = 𝟙 U) ∧
      (∀ i, IsOpenImmersion (s i)) ∧
      ∀ x : (pullback f q : Scheme.{u}), pullback.snd f q x = z default →
        ∃ i, s i (z default) = x := by
  obtain ⟨n, a, ha, _, hsurj⟩ := exists_geometric_sections f b
  have hab (i : Fin n) : (a i ≫ pullback.fst f b) ≫ f = b := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.id_comp]
  obtain ⟨U, q, z, r, hU, hq, hz, hr, hzr⟩ :=
    EtaleFiniteGeometricDiagram.exists_common_affine (fun _ : Fin n ↦ X)
      (fun _ ↦ f) b (fun i ↦ a i ≫ pullback.fst f b) hab
  let s (i : Fin n) : U ⟶ pullback f q :=
    pullback.lift (r i) (𝟙 U) (by rw [Category.id_comp]; exact hr i)
  have hs (i : Fin n) : s i ≫ pullback.snd f q = 𝟙 U := pullback.lift_snd _ _ _
  let m : pullback f b ⟶ pullback f q :=
    pullback.map f b f q (𝟙 X) z (𝟙 Y) (by simp) (by simpa using hz.symm)
  have hm (i : Fin n) : a i ≫ m = z ≫ s i := by
    apply pullback.hom_ext
    · dsimp only [m, s, pullback.map]
      rw [Category.assoc, pullback.lift_fst, Category.comp_id,
        Category.assoc, pullback.lift_fst, hzr]
    · dsimp only [m, s, pullback.map]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ha, Category.id_comp,
        Category.assoc, pullback.lift_snd, Category.comp_id]
  refine ⟨n, U, q, z, s, hU, hq, hz, hs,
    fun i ↦ UnramifiedSectionImmersion.isOpenImmersion _ _ (hs i), ?_⟩
  intro x hx
  have hx' : x ∈ Set.range m := by
    rw [show m = pullback.map f b f q (𝟙 X) z (𝟙 Y) (by simp)
      (by simpa using hz.symm) from rfl, Scheme.Pullback.range_map]
    exact ⟨⟨pullback.fst f q x, rfl⟩, ⟨default, hx.symm⟩⟩
  obtain ⟨y, hy⟩ := hx'
  obtain ⟨i, hi⟩ := hsurj y
  refine ⟨i, ?_⟩
  have h := congrArg (fun g : Spec (.of K) ⟶ pullback f q ↦ g default) (hm i)
  exact h.symm.trans ((congrArg m hi).trans hy)

end FLT.Mazur.EtaleFiniteGeometricFiberSpread
