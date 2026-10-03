/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBranchDifferenceSheaf

/-!
# Structure direct images on cartesian open charts

The comparison is defined on actual sections. It respects scalar actions,
structure inclusions, and branch restrictions in compatible cartesian squares.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.StructureImageOpenChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open StructureDirectImage PolygonStructureInclusion
variable {X Y U V : Scheme.{u}} (p : X ⟶ Y) (p' : U ⟶ V)
  (iU : U ⟶ X) (iV : V ⟶ Y) [IsOpenImmersion iU] [IsOpenImmersion iV]
  (H : IsPullback p' iU iV p)
/-- The cartesian open square identifies the rings on every subopen. -/
def sectionsIso (W : V.Opens) : Γ(X, p ⁻¹ᵁ iV ''ᵁ W) ≅ Γ(U, p' ⁻¹ᵁ W) :=
  X.presheaf.mapIso
    (eqToIso (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op ≪≫
    iU.appIso _
theorem scalar_square (W : V.Opens) :
    (iV.appIso W).inv ≫ p.app _ ≫ (sectionsIso p p' iU iV H W).hom = p'.app W := by
  rw [Iso.inv_comp_eq]
  simp only [Scheme.Hom.app_eq_appLE, sectionsIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op,
    Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE, H.w]
theorem sectionsIso_naturality {W W' : V.Opens} (t : Opposite.op W ⟶ .op W') :
    X.presheaf.map ((TopologicalSpace.Opens.map p.base).map (iV.opensFunctor.map t.unop)).op ≫
      (sectionsIso p p' iU iV H W').hom =
    (sectionsIso p p' iU iV H W).hom ≫
      U.presheaf.map ((TopologicalSpace.Opens.map p'.base).map t.unop).op := by
  simp only [sectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    eqToHom_op, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]
/-- Structure direct image commutes with restriction to this cartesian open chart. -/
def iso : (image p).restrict iV ≅ image p' := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun W ↦ ?_) ?_
  · refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ _ AddCommGrpCat).mapIso
        (sectionsIso p p' iU iV H W.unop)) ?_
    intro (r : Γ(V, W.unop))
    ext (x : Γ(X, p ⁻¹ᵁ iV ''ᵁ W.unop))
    change p'.app _ r * (sectionsIso p p' iU iV H W.unop).hom x =
      (sectionsIso p p' iU iV H W.unop).hom (p.app _ ((iV.appIso W.unop).inv r) * x)
    rw [map_mul]
    exact congrArg (· * (sectionsIso p p' iU iV H W.unop).hom x)
      (congrArg (fun k ↦ k.hom r) (scalar_square p p' iU iV H W.unop)).symm
  · intro W W' t
    ext x
    exact congrArg (fun k ↦ k.hom x) (sectionsIso_naturality p p' iU iV H t)
theorem iso_hom_app (W : V.Opens) (r : Γ(X, p ⁻¹ᵁ iV ''ᵁ W)) :
    (iso p p' iU iV H).hom.val.app (.op W) r =
      (sectionsIso p p' iU iV H W).hom r := rfl
@[reassoc] theorem unit_iso :
    (restrictFunctor iV).map (unitMap p) ≫ (iso p p' iU iV H).hom =
      (restrictUnitIso iV).hom ≫ unitMap p' := by
  apply Scheme.Modules.hom_ext
  intro W
  ext (r : Γ(Y, iV ''ᵁ W))
  change (sectionsIso p p' iU iV H W).hom (p.app (iV ''ᵁ W) r) =
    p'.app W ((iV.appIso W).hom r)
  have he := scalar_square p p' iU iV H W
  rw [Iso.inv_comp_eq] at he
  exact congrArg (fun k ↦ k.hom r) he

variable {Z Z' : Scheme.{u}} (s : Z ⟶ X) (q : Z ⟶ Y) (w : s ≫ p = q)
  (s' : Z' ⟶ U) (q' : Z' ⟶ V) (w' : s' ≫ p' = q')
  (iZ : Z' ⟶ Z) [IsOpenImmersion iZ] (Hq : IsPullback q' iZ iV q)
  (ws : s' ≫ iU = iZ ≫ s)
include ws in
@[reassoc] theorem restriction_iso :
    (restrictFunctor iV).map (restriction s p q w) ≫ (iso q q' iZ iV Hq).hom =
      (iso p p' iU iV H).hom ≫ restriction s' p' q' w' := by
  subst q
  subst q'
  apply Scheme.Modules.hom_ext
  intro W
  ext (r : Γ(X, p ⁻¹ᵁ iV ''ᵁ W))
  change (sectionsIso (s ≫ p) (s' ≫ p') iZ iV Hq W).hom
    (s.app (p ⁻¹ᵁ iV ''ᵁ W) r) =
      s'.app (p' ⁻¹ᵁ W) ((sectionsIso p p' iU iV H W).hom r)
  have he : s.app (p ⁻¹ᵁ iV ''ᵁ W) ≫
      (sectionsIso (s ≫ p) (s' ≫ p') iZ iV Hq W).hom =
    (sectionsIso p p' iU iV H W).hom ≫ s'.app (p' ⁻¹ᵁ W) := by
    simp only [sectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
      eqToIso.hom, eqToHom_op, Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE, ws]
    change s.appLE _ _ _ ≫ iZ.appLE _ _ _ = _
    rw [Scheme.Hom.appLE_comp_appLE]
    rfl
  exact congrArg (fun k ↦ k.hom r) he
end FLT.Mazur.StructureImageOpenChart
