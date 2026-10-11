/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSeparablePointFactor
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finite separable witnesses for scheme points

Every separable point of a scheme locally of finite type over a field
factors, as the same entire morphism, through a finite separable subfield.
An affine neighborhood of its image supplies the finite generating family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.LocallyFiniteTypeSeparablePointFactor
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
  {X : Scheme}

/-- The original scheme point and its base map factor through a finite separable subextension. -/
theorem exists_factor (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : Spec (.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ (L : IntermediateField k K) (y : Spec (.of L) ⟶ X),
      Module.Finite k L ∧ Algebra.IsSeparable k L ∧
      y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ y = x := by
  obtain ⟨A, j, hj, u, hu⟩ := X.exists_Spec_apply_eq (x default)
  let _ := hj
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    exact ⟨u, hu.trans (congrArg x (Subsingleton.elim default w))⟩
  let a := IsOpenImmersion.lift j x hr
  have ha : a ≫ j = x := IsOpenImmersion.lift_fac j x hr
  obtain ⟨r, hr⟩ := Spec.map_surjective (j ≫ f)
  let _ := r.hom.toAlgebra
  have hft : LocallyOfFiniteType (Spec.map r) := hr.symm ▸ inferInstance
  let _ : Algebra.FiniteType k A := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft)
  obtain ⟨q, hq⟩ := Spec.map_surjective a
  have hb : q.hom.comp r.hom = algebraMap k K := by
    have h : Spec.map (r ≫ q) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      rw [Spec.map_comp, hq, hr, ← Category.assoc, ha, hx]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  let qA : A →ₐ[k] K :=
    { q.hom with commutes' := fun t ↦ RingHom.congr_fun hb t }
  obtain ⟨L, q₀, hfin, hsep, hfac⟩ := FiniteSeparablePointFactor.exists_factor qA
  refine ⟨L, Spec.map (CommRingCat.ofHom q₀.toRingHom) ≫ j, hfin, hsep, ?_, ?_⟩
  · rw [Category.assoc, ← hr, ← Spec.map_comp]
    exact congrArg (fun t ↦ Spec.map (CommRingCat.ofHom t)) q₀.comp_algebraMap
  · rw [← Category.assoc, ← Spec.map_comp]
    have h : (algebraMap L K).comp q₀.toRingHom = q.hom :=
      congrArg AlgHom.toRingHom hfac
    change Spec.map (CommRingCat.ofHom ((algebraMap L K).comp q₀.toRingHom)) ≫ j = x
    rw [h]
    change Spec.map q ≫ j = x
    rw [hq, ha]

end FLT.Mazur.LocallyFiniteTypeSeparablePointFactor
