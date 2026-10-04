/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleRestrict

/-!
# Unit coordinates give section isomorphisms

A section whose coordinate under an actual sheaf trivialization is a unit
trivializes the sheaf on that open.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}}

/-- Multiplication by a unit section is an isomorphism of sheaves on its open. -/
lemma sectionHom_isIso_of_isUnit (U : X.Opens) (r : Γ(X, U)) (hr : IsUnit r) :
    IsIso (sectionHom (structureModule X) U r) := by
  apply (Scheme.Modules.Hom.isIso_iff_isIso_app).mpr
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  have hv := hr.map (X.presheaf.map (homOfLE (U.ι_image_le V)).op).hom
  change Function.Bijective (fun a : Γ(U.toScheme, V) ↦
    (U.ι.appIso V).inv a * X.presheaf.map (homOfLE (U.ι_image_le V)).op r)
  obtain ⟨v, hv⟩ := hv
  rw [← hv]
  exact (Units.mulRight v).bijective.comp
    (ConcreteCategory.bijective_of_isIso (U.ι.appIso V).inv)

/-- A sheaf trivialization with unit coordinate makes the actual section invertible. -/
lemma sectionHom_isIso_of_coordinate {M : X.Modules} (U : X.Opens)
    (e : M ≅ structureModule X) (s : Γ(M, U)) (hs : IsUnit (show Γ(X, U) from e.hom.app U s)) :
    IsIso (sectionHom M U s) := by
  have := sectionHom_isIso_of_isUnit U (e.hom.app U s) hs
  have hc : IsIso (sectionHom M U s ≫ (restrictFunctor U.ι).map e.hom) := by
    rw [sectionHom_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((restrictFunctor U.ι).map e.hom)

/-- An invertible local pairing with unit value makes the section invertible. -/
lemma sectionHom_isIso_of_pairing {M : X.Modules} (U : X.Opens)
    (e : M.restrict U.ι ≅ structureModule U.toScheme) (s : Γ(M, U))
    (hs : IsUnit (moduleDualEval M U e.hom s)) : IsIso (sectionHom M U s) := by
  have := sectionHom_isIso_of_isUnit U (moduleDualEval M U e.hom s) hs
  have hc : IsIso (sectionHom M U s ≫ e.hom) := by
    rw [moduleDualEval_sectionHom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

/-- On a subopen, linear coordinates of a section morphism multiply its section coordinate. -/
lemma sectionHom_app_coordinate (M : X.Modules) (U : X.Opens) (s : Γ(M, U))
    (V : U.toScheme.Opens)
    (e : Γ(M, U.ι ''ᵁ V) ≃ₗ[Γ(X, U.ι ''ᵁ V)] Γ(X, U.ι ''ᵁ V))
    (r : Γ(U.toScheme, V)) :
    e ((sectionHom M U s).app V r) =
      (U.ι.appIso V).inv r * e (M.presheaf.map (homOfLE (U.ι_image_le V)).op s) := by
  rw [sectionHom_app]
  erw [M.smul_restrictAppIso_hom_apply U.ι V r]
  exact e.map_smul ((U.ι.appIso V).inv r) _

/-- Unit coordinates on affine subopens make the section morphism an isomorphism. -/
theorem sectionHom_isIso_of_affine_coordinates (M : X.Modules) (U : X.Opens) (s : Γ(M, U))
    (e : ∀ V : U.toScheme.affineOpens,
      Γ(M, U.ι ''ᵁ V.1) ≃ₗ[Γ(X, U.ι ''ᵁ V.1)] Γ(X, U.ι ''ᵁ V.1))
    (hs : ∀ V, IsUnit (e V (M.presheaf.map (homOfLE (U.ι_image_le V.1)).op s))) :
    IsIso (sectionHom M U s) := by
  let φ := (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map (sectionHom M U s)
  have hφ : IsIso φ := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun V : U.toScheme.affineOpens ↦ V.1)
      (by simpa using U.toScheme.isBasis_affineOpens)
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    apply (Function.Bijective.of_comp_iff' (e V).bijective _).mp
    change Function.Bijective (fun r : Γ(U.toScheme, V.1) ↦
      e V ((sectionHom M U s).app V.1 r))
    simp only [sectionHom_app_coordinate]
    simpa only [Function.comp_def, Units.mulRight_apply, IsUnit.unit_spec] using
      ((hs V).unit.mulRight).bijective.comp
      (ConcreteCategory.bijective_of_isIso (U.ι.appIso V.1).inv)
  apply (Scheme.Modules.Hom.isIso_iff_isIso_app).mpr
  intro V
  exact inferInstanceAs (IsIso (φ.hom.app (op V)))

/-- A local sheaf trivialization gives surjective coordinate evaluation. -/
lemma moduleDualEval_surjective_of_iso (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ structureModule U.toScheme) :
    Function.Surjective (moduleDualEval M U e.hom) := by
  intro r
  let j : U.ι ''ᵁ (⊤ : U.toScheme.Opens) ⟶ U := eqToHom U.ι_image_top
  let t := e.inv.app ⊤ (U.topIso.inv r)
  refine ⟨M.presheaf.map (inv j.op) t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso U.topIso.inv).injective
  have he := moduleDualEval_app M U e.hom (M.presheaf.map (inv j.op) t) ⊤
  change e.hom.app ⊤ (M.presheaf.map j.op (M.presheaf.map (inv j.op) t)) =
    U.topIso.inv (moduleDualEval M U e.hom (M.presheaf.map (inv j.op) t)) at he
  rw [← Functor.map_comp_apply, IsIso.inv_hom_id, M.presheaf.map_id,
    ConcreteCategory.id_apply] at he
  rw [← he]
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app ⊤) e.inv_hom_id) _

/-- Any linear section coordinates detect generators once an actual trivialization exists. -/
lemma sectionHom_isIso_of_linear_coordinate (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ structureModule U.toScheme)
    (c : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U)) (s : Γ(M, U)) (hs : IsUnit (c s)) :
    IsIso (sectionHom M U s) := by
  apply sectionHom_isIso_of_pairing U e s
  obtain ⟨t, ht⟩ := moduleDualEval_surjective_of_iso M U e (1 : Γ(X, U))
  obtain ⟨v, hv⟩ := hs
  have hst : (c t * (↑v⁻¹ : Γ(X, U))) • s = t := by
    apply c.injective
    rw [c.map_smul, smul_eq_mul, ← hv]
    simp
  have he := congrArg (moduleDualEval M U e.hom) hst
  rw [(moduleDualEval M U e.hom).map_smul, ht] at he
  exact IsUnit.of_mul_eq_one_right _ he

end FLT.Mazur.FCurve
