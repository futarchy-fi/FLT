/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.InertiaDescentField
public import FLT.GroupScheme.FiniteFlatRestrictedScalarExtension

/-!
# Actual action agreement over the normal inertia descent field

Normality makes the chosen embedding of algebraic closures preserve the
finite descent field as a set. Thus restriction of its absolute Galois
group fixes the original copy of that field and acts like inertia.
-/

@[expose] public noncomputable section

namespace InertiaDescent

variable {K X : Type} [Field K] [PerfectField K] [AddCommGroup X]
  [DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X]
  [Finite X] [ContinuousSMulDiscrete (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X]
  (I : Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) [I.Normal]

/-- Restriction from the actual descent field fixes its original normal copy. -/
theorem map_mem_fixingSubgroup
    (σ : Field.absoluteGaloisGroup (field (X := X) I)) :
    Field.absoluteGaloisGroup.map (algebraMap K (field (X := X) I)) σ ∈
      (field (X := X) I).fixingSubgroup := by
  let L := field (X := X) I
  let e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L :=
    { __ := AlgebraicClosure.map (algebraMap K L)
      commutes' := AlgebraicClosure.map_algebraMap _ }
  intro x
  apply e.injective
  change e (Field.absoluteGaloisGroup.map (algebraMap K L) σ x) = e x
  have he : e (Field.absoluteGaloisGroup.map (algebraMap K L) σ x) = σ (e x) :=
    Field.absoluteGaloisGroup.lift_map _ _ _
  rw [he]
  have hx : algebraMap L (AlgebraicClosure L) (e.restrictNormal L x) = e x :=
    e.restrictNormal_commutes L x
  rw [← hx]
  exact σ.commutes _

/-- The actual absolute-Galois restriction acts through the original inertia image. -/
theorem exists_inertia_action_map
    (σ : Field.absoluteGaloisGroup (field (X := X) I)) :
    ∃ τ : I, ∀ x : X,
      Field.absoluteGaloisGroup.map (algebraMap K (field (X := X) I)) σ • x = τ.1 • x := by
  have hσ := map_mem_fixingSubgroup (X := X) I σ
  rw [fixingSubgroup_field] at hσ
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hσ
  refine ⟨⟨b, hb⟩, fun x ↦ ?_⟩
  rw [← hab, mul_smul]
  exact Equiv.congr_fun ha (b • x)

end InertiaDescent
