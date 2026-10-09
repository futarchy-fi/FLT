/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentFamilyLineData
public import FLT.Mazur.SchemeFppfFamilyOverlapMapAssembly

/-!
# The category of independent family line data

Morphisms are independently supplied member maps satisfying original pair
squares. Assembly constructs an actual functor to geometric family data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard SchemeGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} {𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X}

/-- A map retains precisely the original pair compatibility equations. -/
abbrev Hom (D E : IndependentLineData 𝒰) :=
  {f : ∀ i, (D.obj i).val ⟶ (E.obj i).val // PairMapCompatible 𝒰 D.overlap E.overlap f}

instance : Category (IndependentLineData 𝒰) where
  Hom := Hom
  id D := ⟨fun i ↦ 𝟙 (D.obj i).val, fun ij ↦ by simp⟩
  comp f g := ⟨fun i ↦ f.val i ≫ g.val i, fun ij ↦ by
    dsimp only
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc, f.property ij, Category.assoc, g.property ij,
      ← Category.assoc]⟩
  id_comp f := Subtype.ext (funext fun i ↦ Category.id_comp (f.val i))
  comp_id f := Subtype.ext (funext fun i ↦ Category.comp_id (f.val i))
  assoc f g h := Subtype.ext (funext fun i ↦ Category.assoc (f.val i) (g.val i) (h.val i))

/-- Independent descent maps are determined by their original component maps. -/
@[ext]
lemma hom_ext {D E : IndependentLineData 𝒰} {f g : D ⟶ E}
    (h : ∀ i, f.val i = g.val i) : f = g := Subtype.ext (funext h)

/-- Forget pair equations while retaining all original line bundles and maps. -/
def members : IndependentLineData 𝒰 ⥤ (∀ i, LineBundleCat (𝒰.X i)) where
  obj D := D.obj
  map f i := InducedCategory.homMk (f.val i)

/-- Assemble original objects and compatible maps into actual geometric family data. -/
def assemble : IndependentLineData 𝒰 ⥤ FamilyLineData 𝒰 where
  obj D := D.toFamily
  map f := ⟨SchemeCoproductModuleGluing.map 𝒰.X f.val,
    assembledOverlap_map 𝒰 _ _ f.val f.property⟩
  map_id _ := LineData.hom_ext _ (SchemeCoproductModuleGluing.map_id 𝒰.X)
  map_comp f g := LineData.hom_ext _ (SchemeCoproductModuleGluing.map_comp 𝒰.X f.val g.val)

/-- Recover every original member module naturally after assembly. -/
def assemblyMemberRecovery (i : 𝒰.I₀) :
    assemble ⋙ component 𝒰 i ≅ members ⋙ (Pi.eval _ i) ⋙ lineBundleForget (𝒰.X i) :=
  NatIso.ofComponents (fun D ↦ D.memberRecovery i) (fun f ↦
    SchemeCoproductModuleGluing.map_recovery 𝒰.X f.val i)

/-- Effective descent is functorial for independently supplied family data. -/
def descend : IndependentLineData 𝒰 ⥤ LineBundleCat X :=
  assemble ⋙ (familyLineEquivalence 𝒰).inverse

/-- Effective descent recovers each independently supplied member, naturally in maps. -/
def descentMemberRecovery (i : 𝒰.I₀) :
    descend ⋙ lineBundleForget X ⋙ pullback (𝒰.f i) ≅
      members ⋙ (Pi.eval _ i) ⋙ lineBundleForget (𝒰.X i) :=
  Functor.isoWhiskerLeft assemble (componentRecovery 𝒰 i) ≪≫ assemblyMemberRecovery i

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
