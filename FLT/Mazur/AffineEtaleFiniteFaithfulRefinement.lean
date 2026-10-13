/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleTranslationFiniteBranch
public import FLT.Mazur.FiniteEtaleWholeFiberNeighborhood

/-!
# Finite faithful refinements inside arbitrary translation neighborhoods

Every point in an affine etale translation admits an affine etale refinement
inside any prescribed open neighborhood. Over a constructed affine etale base
this refinement is finite and surjective. The original structural square and
chosen point are retained. The base changes; finiteness over the old base is
not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EtaleTranslationBranch
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {V : Scheme.{u}}
  (g : V ⟶ Spec (.of R)) [IsAffine V] [Etale g]

/-- Actual finite faithful affine refinements exist inside every original translation open. -/
theorem exists_finite_faithful_refinement (v : V) (U : V.Opens) (hv : v ∈ U) :
    ∃ (T W : Scheme.{u}) (_ : IsAffine T) (_ : IsAffine W)
      (b : T ⟶ Spec (.of R)) (a : W ⟶ V) (t : W ⟶ T),
      Etale b ∧ Etale a ∧ Etale t ∧ IsFinite t ∧ Surjective t ∧
      a ≫ g = t ≫ b ∧ Set.range a ⊆ U ∧ ∃ w : W, a w = v := by
  obtain ⟨S, hS, hRS, hEt, Z, hZ, a, t, ha, ht, hfin, hsq, z, hz, huniq⟩ :=
    exists_affine_finite_etale_neighborhood g v
  let b := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let _ : Etale b := HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr hEt)
  obtain ⟨r, hr, hU, hA, hfin', ht', hsurj⟩ :=
    FiniteEtaleWholeFiberNeighborhood.exists_finite_faithful_restriction_of_unique
      t z huniq (a ⁻¹ᵁ U) (by change a z ∈ U; rwa [hz])
  let T := (Spec (.of S)).basicOpen r
  let W := t ⁻¹ᵁ T
  let _ : IsAffine T.toScheme := (isAffineOpen_top (Spec (.of S))).basicOpen r
  have hsquare : (W.ι ≫ a) ≫ g = (t ∣_ T) ≫ T.ι ≫ b := by
    rw [Category.assoc, hsq, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  refine ⟨T.toScheme, W.toScheme, inferInstance, hA, T.ι ≫ b, W.ι ≫ a, t ∣_ T,
    inferInstance, inferInstance, ht', hfin', hsurj, hsquare, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    exact hU w.property
  · exact ⟨⟨z, hr⟩, hz⟩

/-- These constructed refinements retain every original translation point, without a global cover
assumption on the translation itself. -/
theorem finite_faithful_refinements_cover (v : V) :
    ∃ (T W : Scheme.{u}) (_ : IsAffine T) (_ : IsAffine W)
      (b : T ⟶ Spec (.of R)) (a : W ⟶ V) (t : W ⟶ T),
      Etale b ∧ Etale a ∧ Etale t ∧ IsFinite t ∧ Surjective t ∧
      a ≫ g = t ≫ b ∧ ∃ w : W, a w = v := by
  obtain ⟨T, W, hT, hW, b, a, t, hb, ha, ht, hfin, hsurj, hsq, _, hw⟩ :=
    exists_finite_faithful_refinement g v ⊤ trivial
  exact ⟨T, W, hT, hW, b, a, t, hb, ha, ht, hfin, hsurj, hsq, hw⟩

end FLT.Mazur.EtaleTranslationBranch
