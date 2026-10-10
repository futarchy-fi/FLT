/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentFamilyEquivalence

/-!
# Effective independent recovery retains the original pair equations

Lift the actual family counit through fully faithful assembly. Its member maps
are the original effective recoveries, so their pair equations are inherited.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} {𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X}
variable (D : IndependentLineData 𝒰)

/-- The original effective counit lifts to the original independent data. -/
def effectiveRecoveryIso : canonicalObj 𝒰 D.descended ≅ D :=
  assemble.preimageIso ((canonicalAssemblyIso 𝒰 D.descended).symm ≪≫ D.descendedComparison)

/-- Assembly of the lifted counit retains its prescribed source map. -/
lemma effectiveRecoveryIso_source :
    (canonicalSourceIso 𝒰 D.descended).hom ≫
      SchemeCoproductModuleGluing.map 𝒰.X (D.effectiveRecoveryIso.hom.val) =
        D.descendedComparison.hom.val := by
  have h := congrArg Subtype.val (assemble.map_preimage
    ((canonicalAssemblyIso 𝒰 D.descended).symm ≪≫ D.descendedComparison).hom)
  change SchemeCoproductModuleGluing.map 𝒰.X D.effectiveRecoveryIso.hom.val =
    (canonicalSourceIso 𝒰 D.descended).inv ≫ D.descendedComparison.hom.val at h
  rw [h, Iso.hom_inv_id_assoc]

/-- The lifted independent counit has exactly the originally constructed member maps. -/
lemma effectiveRecoveryIso_member (i : 𝒰.I₀) :
    D.effectiveRecoveryIso.hom.val i = (D.descendedMemberRecovery i).hom := by
  apply (cancel_epi ((canonicalComponent 𝒰 i).app D.descended).hom).mp
  change ((canonicalComponent 𝒰 i).app D.descended).hom ≫
    D.effectiveRecoveryIso.hom.val i =
    ((canonicalComponent 𝒰 i).app D.descended).hom ≫
      (((canonicalComponent 𝒰 i).app D.descended).inv ≫
        (pullback (Limits.Sigma.ι 𝒰.X i)).map D.descendedComparison.hom.val) ≫
          (D.memberRecovery i).hom
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  change (SheafPullbackPathComparison.comparison (Limits.Sigma.ι 𝒰.X i)
    (projection 𝒰) (𝒰.f i) (inclusion_projection 𝒰 i)).hom.app D.descended.val ≫ _ = _
  have hr := SchemeCoproductModuleGluing.map_recovery 𝒰.X D.effectiveRecoveryIso.hom.val i
  change (pullback (Limits.Sigma.ι 𝒰.X i)).map
      (SchemeCoproductModuleGluing.map 𝒰.X D.effectiveRecoveryIso.hom.val) ≫
        (D.memberRecovery i).hom =
      ((canonicalObj 𝒰 D.descended).memberRecovery i).hom ≫
        D.effectiveRecoveryIso.hom.val i at hr
  rw [← canonicalSourceIso_recovery, Category.assoc, ← hr,
    ← Category.assoc, ← Functor.map_comp, D.effectiveRecoveryIso_source]

/-- Original effective member recoveries intertwine the supplied original pair maps. -/
lemma descendedMemberRecovery_pair :
    PairMapCompatible 𝒰 (canonicalObj 𝒰 D.descended).overlap D.overlap
      (fun i ↦ (D.descendedMemberRecovery i).hom) := by
  intro ij
  have h := D.effectiveRecoveryIso.hom.property ij
  dsimp only [PairMapCompatible] at h ⊢
  simpa only [D.effectiveRecoveryIso_member] using h

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
