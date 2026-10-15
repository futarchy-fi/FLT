/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Finite coefficient descent of algebraic geometric points

A point over an algebraic coefficient extension on an original locally
finite type scheme factors through a finite extension of the base field.
The factorization is of the whole morphism, not just its image point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AlgebraicPointFiniteDescent
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] [Algebra k K]
  {X : Scheme} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- The original residue-field structure is essentially of finite type over the base field. -/
theorem residue_essFiniteType (x : X) (α : CommRingCat.of k ⟶ X.residueField x)
    (hα : Spec.map α = X.fromSpecResidueField x ≫ f) : α.hom.EssFiniteType := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective ((Spec (.of k)).fromSpecResidueField (f x))
  have hb : IsClosedImmersion ((Spec (.of k)).fromSpecResidueField (f x)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_singleton (x := f x))
  have hβf : β.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hβ]
    infer_instance
  have he : α = β ≫ f.residueFieldMap x := by
    apply Spec.map_injective
    rw [Spec.map_comp, hβ, f.SpecMap_residueFieldMap_fromSpecResidueField, hα]
  rw [he]
  exact hβf.essFiniteType.comp (LocallyOfFiniteType.stalkMap f x).residueFieldMap

/-- Algebraic geometric points descend to a finite residue-field extension with their full map. -/
theorem exists_finite_factor [Algebra.IsAlgebraic k K]
    (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L)
      (i : L →ₐ[k] K) (q : Spec (.of L) ⟶ X),
      q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        Spec.map (CommRingCat.ofHom i.toRingHom) ≫ q = p := by
  obtain ⟨⟨x, u⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective p
  change Spec.map u ≫ X.fromSpecResidueField x ≫ f = _ at hp
  obtain ⟨α, hα⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  let _ : Algebra k (X.residueField x) := α.hom.toAlgebra
  have hu : u.hom.comp α.hom = algebraMap k K := by
    change (α ≫ u).hom = (CommRingCat.ofHom (algebraMap k K)).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    simpa only [Spec.map_comp, hα] using hp
  let i : X.residueField x →ₐ[k] K :=
    { u.hom with commutes' := fun r ↦ RingHom.congr_fun hu r }
  let _ : Algebra.IsAlgebraic k (X.residueField x) :=
    Algebra.IsAlgebraic.of_injective i i.injective
  let _ : Algebra.EssFiniteType k (X.residueField x) := residue_essFiniteType f x α hα
  let _ : Module.Finite k (X.residueField x) :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact ⟨X.residueField x, inferInstance, inferInstance, inferInstance,
    i, X.fromSpecResidueField x, hα.symm, rfl⟩

end FLT.Mazur.AlgebraicPointFiniteDescent
