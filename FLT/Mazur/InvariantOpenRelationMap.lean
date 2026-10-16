/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenRelationFunctions
public import FLT.Mazur.SchemeRelationFunctionDiagram

/-!
# Maps between full relations on invariant source opens

An original two-endpoint diagram restricts to compatible invariant source
opens. The relation map and both endpoint squares are constructed, rather
than supplied as extra compatibility data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantOpenRelationDiagram
open SchemeFunctionGroundChange
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{0}} {A D B E : Over S}
  (p q : D ⟶ A) (r s : E ⟶ B) (u : B ⟶ A) (v : E ⟶ D)
  (hp : v ≫ p = r ≫ u) (hq : v ≫ q = s ≫ u)
  (U : A.left.Opens) (V : B.left.Opens)
  (hU : p.left ⁻¹ᵁ U = q.left ⁻¹ᵁ U)
  (hV : r.left ⁻¹ᵁ V = s.left ⁻¹ᵁ V) (hUV : V ≤ u.left ⁻¹ᵁ U)

/-- Restrict the original source map over the unchanged coefficient scheme. -/
def sourceMap : source V ⟶ source U :=
  Over.homMk (u.left.resLE U V hUV) (by
    change _ ≫ U.ι ≫ A.hom = _
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w u]
    rfl)

include hp hUV in
/-- The first endpoint square supplies the domain for the full restricted relation map. -/
theorem relationMap_domain : r.left ⁻¹ᵁ V ≤ v.left ⁻¹ᵁ (p.left ⁻¹ᵁ U) := by
  calc
    r.left ⁻¹ᵁ V ≤ r.left ⁻¹ᵁ (u.left ⁻¹ᵁ U) := r.left.preimage_mono hUV
    _ = v.left ⁻¹ᵁ (p.left ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      have h := congrArg Over.Hom.left hp
      exact congrArg (fun a : E.left ⟶ A.left ↦ a ⁻¹ᵁ U) h.symm

/-- The entire original relation map on the specified invariant domains. -/
def relationMap : relation r V ⟶ relation p U :=
  Over.homMk (v.left.resLE _ _ (relationMap_domain p r u v hp U V hUV)) (by
    change _ ≫ (p.left ⁻¹ᵁ U).ι ≫ D.hom = _
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w v]
    rfl)

/-- Restricted source maps retain their original ambient map. -/
@[reassoc]
theorem sourceMap_inclusion : sourceMap u U V hUV ≫ sourceInclusion U =
    sourceInclusion V ≫ u := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι u.left hUV

/-- Restricted relation maps retain their original ambient arrow. -/
@[reassoc]
theorem relationMap_inclusion : relationMap p r u v hp U V hUV ≫ relationInclusion p U =
    relationInclusion r V ≫ v := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι v.left _

instance sourceInclusion_mono : Mono (sourceInclusion U) := Over.mono_of_mono_left _

/-- The restricted first endpoint square is constructed from the ambient square. -/
@[reassoc]
theorem map_fst : relationMap p r u v hp U V hUV ≫ fst p U =
    fst r V ≫ sourceMap u U V hUV := by
  apply (cancel_mono (sourceInclusion U)).mp
  rw [Category.assoc, ← inclusion_fst, ← Category.assoc, relationMap_inclusion,
    Category.assoc, hp, ← Category.assoc, inclusion_fst, Category.assoc,
    Category.assoc, sourceMap_inclusion]

include hq in
/-- The restricted second endpoint square retains the independent ambient endpoint. -/
@[reassoc]
theorem map_snd : relationMap p r u v hp U V hUV ≫ snd p q U hU =
    snd r s V hV ≫ sourceMap u U V hUV := by
  apply (cancel_mono (sourceInclusion U)).mp
  rw [Category.assoc, ← inclusion_snd, ← Category.assoc, relationMap_inclusion,
    Category.assoc, hq, ← Category.assoc, inclusion_snd, Category.assoc,
    Category.assoc, sourceMap_inclusion]

attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra

/-- Actual pullback in the source function coordinates of the two restricted schemes. -/
theorem sourceMap_function (a : Γ(A.left, U)) :
    sectionMap (sourceMap u U V hUV) (sourceFunctions U a) =
      sourceFunctions V (u.left.appLE U V hUV a) := by
  change (u.left.resLE U V hUV).appTop (U.topIso.inv a) = V.topIso.inv _
  simp only [Scheme.Hom.resLE_app_top, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

/-- The full invariant function map between the constructed restricted relations. -/
def functionsMap :
    AlgHom.equalizer (sectionMap (fst p U)) (sectionMap (snd p q U hU)) →ₐ[Γ(S, ⊤)]
      AlgHom.equalizer (sectionMap (fst r V)) (sectionMap (snd r s V hV)) :=
  SchemeRelationFunctionDiagram.invariantMap _ _ _ _ (sourceMap u U V hUV)
    (relationMap p r u v hp U V hUV) (map_fst p r u v hp U V hUV)
    (map_snd p q r s u v hp hq U V hU hV hUV)

end FLT.Mazur.InvariantOpenRelationDiagram
