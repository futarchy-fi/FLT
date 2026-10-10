/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyOverlapAssembly
public import FLT.Mazur.SchemeOverlapRefinement

/-!
# Recovery of the assembled overlap on an original member

Refinement to one member of the coproduct agrees with that member's
independently supplied self-overlap, through the original recovery isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
open SchemeOverlapRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (M : ∀ i, (𝒰.X i).Modules)

/-- The square for refinement to a single original member. -/
lemma member_square (i : 𝒰.I₀) :
    𝒰.f i ≫ 𝟙 X = Limits.Sigma.ι 𝒰.X i ≫ projection 𝒰 := by simp

/-- The refinement overlap is the original self-pair chart. -/
lemma member_overlapMap (i : 𝒰.I₀) :
    overlapMap (projection 𝒰) (𝒰.f i) (𝟙 X) (Limits.Sigma.ι 𝒰.X i)
      (member_square 𝒰 i) = pairMap 𝒰 (i, i) := rfl

/-- The left recovery cancels the refinement's first projection comparison. -/
@[reassoc]
lemma firstIso_memberRecovery (i : 𝒰.I₀) :
    (firstIso (projection 𝒰) (𝒰.f i) (𝟙 X) (Limits.Sigma.ι 𝒰.X i)
      (member_square 𝒰 i)).hom.app (SchemeCoproductModuleGluing.assembled 𝒰.X M) ≫
        (pairLeftRecovery 𝒰 M (i, i)).hom =
      (pullback (Limits.pullback.fst (𝒰.f i) (𝒰.f i))).map
        (SchemeCoproductModuleGluing.recovery 𝒰.X M i).hom := by
  simp only [firstIso, pairLeftRecovery, member_overlapMap, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [pullbackCongr, eqToIso, ← NatTrans.comp_app_assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Iso.hom_inv_id, NatTrans.id_app]

/-- The right recovery cancels the refinement's second projection comparison. -/
@[reassoc]
lemma secondIso_memberRecovery (i : 𝒰.I₀) :
    (secondIso (projection 𝒰) (𝒰.f i) (𝟙 X) (Limits.Sigma.ι 𝒰.X i)
      (member_square 𝒰 i)).hom.app (SchemeCoproductModuleGluing.assembled 𝒰.X M) ≫
        (pairRightRecovery 𝒰 M (i, i)).hom =
      (pullback (Limits.pullback.snd (𝒰.f i) (𝒰.f i))).map
        (SchemeCoproductModuleGluing.recovery 𝒰.X M i).hom := by
  simp only [secondIso, pairRightRecovery, member_overlapMap, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [pullbackCongr, eqToIso, ← NatTrans.comp_app_assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Iso.hom_inv_id, NatTrans.id_app]

/-- The original member recovery intertwines refinement with its supplied self-overlap. -/
lemma refined_member_overlap (e : PairIsomorphisms 𝒰 M) (i : 𝒰.I₀) :
    (refine (projection 𝒰) (𝒰.f i) (𝟙 X) (Limits.Sigma.ι 𝒰.X i)
      (member_square 𝒰 i) (assembledOverlap 𝒰 M e)).hom ≫
        (pullback (Limits.pullback.snd (𝒰.f i) (𝒰.f i))).map
          (SchemeCoproductModuleGluing.recovery 𝒰.X M i).hom =
    (pullback (Limits.pullback.fst (𝒰.f i) (𝒰.f i))).map
      (SchemeCoproductModuleGluing.recovery 𝒰.X M i).hom ≫ (e (i, i)).hom := by
  have hf := refine_hom (projection 𝒰) (𝒰.f i) (𝟙 X) (Limits.Sigma.ι 𝒰.X i)
    (member_square 𝒰 i) (assembledOverlap 𝒰 M e)
  dsimp only [Iso.app_hom] at hf
  rw [← secondIso_memberRecovery 𝒰 M i, ← Category.assoc, hf]
  simp only [Category.assoc, member_overlapMap]
  rw [assembledOverlap_recovery, firstIso_memberRecovery_assoc]

end FLT.Mazur.SchemeFppfFamily
