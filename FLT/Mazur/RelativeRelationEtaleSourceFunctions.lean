/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationOpenSourceFunctions
public import FLT.Mazur.SchemeRelationCoverSourceFunctions

/-!
# Original invariant functions on an etale source

An etale source covers its open image. Descent along this cover identifies
functions compatible with the full original relation with sections on the
original orbit image, retaining the actual geometric pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y X : Scheme.{u}} (k : Y ⟶ X) [Etale k]

/-- The open image of an etale map, without a monicity assumption. -/
def etaleSourceImage : X.Opens := ⟨Set.range k, k.isOpenMap.isOpen_range⟩

/-- The actual etale source surjects onto its open scheme image. -/
def etaleSourceImageMap : Y ⟶ (etaleSourceImage k).toScheme :=
  IsOpenImmersion.lift (etaleSourceImage k).ι k (by rw [Scheme.Opens.range_ι]; rfl)

@[reassoc]
theorem etaleSourceImageMap_ι : etaleSourceImageMap k ≫ (etaleSourceImage k).ι = k :=
  IsOpenImmersion.lift_fac _ _ _

instance etaleSourceImageMap_etale : Etale (etaleSourceImageMap k) := by
  let _ : Etale (etaleSourceImageMap k ≫ (etaleSourceImage k).ι) := by
    rw [etaleSourceImageMap_ι]
    infer_instance
  exact Etale.of_comp _ (etaleSourceImage k).ι

instance etaleSourceImageMap_surjective : Surjective (etaleSourceImageMap k) where
  surj x := by
    obtain ⟨y, hy⟩ := x.property
    refine ⟨y, Subtype.ext ?_⟩
    exact (congrArg (fun g ↦ g y) (etaleSourceImageMap_ι k)).trans hy

/-- Pullback from image coordinates is the original source's map on regular functions. -/
theorem etaleSourceImageMap_appTop (v : Γ(X, (etaleSourceImage k)))
    (h : ⊤ ≤ k ⁻¹ᵁ (etaleSourceImage k)) :
    (etaleSourceImageMap k).appTop ((etaleSourceImage k).topIso.inv v) =
      k.appLE (etaleSourceImage k) ⊤ h v := by
  have ht : (etaleSourceImage k).topIso.inv =
      (etaleSourceImage k).ι.appLE (etaleSourceImage k) ⊤
        (etaleSourceImage k).ι_preimage_self.ge := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
    congr 1
  rw [ht]
  have hc := Scheme.Hom.appLE_comp_appLE (etaleSourceImageMap k) (etaleSourceImage k).ι
    (etaleSourceImage k) ⊤ ⊤ (etaleSourceImage k).ι_preimage_self.ge le_rfl
  have he : (etaleSourceImageMap k).appLE ⊤ ⊤ le_rfl =
      (etaleSourceImageMap k).appTop := by simp [Scheme.Hom.appLE]
  simp only [etaleSourceImageMap_ι, he] at hc
  exact congrArg (fun g ↦ g v) hc

variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  {T : Scheme.{u}} (j : T ⟶ U.left) [Etale j] [Etale q.left]

/-- Full original functions on an etale source equal the original orbit-image sections. -/
def etaleSourceFunctionEquiv :
    (invariantSheaf e).obj.obj (op (orbitImageOpen e hq (etaleSourceImage j))) ≃+*
      compatibleFunctions (SchemeRelationRestriction.fst p.left q.left j)
        (SchemeRelationRestriction.snd p.left q.left j) :=
  (saturatedSheafFunctionEquiv e hq (etaleSourceImage j)).trans
    (SchemeRelationRestriction.sourceCoverEquiv p.left q.left e.r.left
      (congrArg Over.Hom.left e.reflexivity₁) (congrArg Over.Hom.left e.reflexivity₂)
      j (etaleSourceImage j).ι (etaleSourceImageMap j) (etaleSourceImageMap_ι j))

/-- The invariant comparison is the unchanged original source pullback. -/
theorem etaleSourceFunctionEquiv_appLE
    (t : (invariantSheaf e).obj.obj (op (orbitImageOpen e hq (etaleSourceImage j))))
    (h : ⊤ ≤ j ⁻¹ᵁ (pullOpen e (orbitImageOpen e hq (etaleSourceImage j))).val) :
    (etaleSourceFunctionEquiv e hq j t).val =
      j.appLE _ ⊤ h
        ((invariantInclusion e).hom.app (op (orbitImageOpen e hq (etaleSourceImage j))) t) := by
  change (etaleSourceImageMap j).appTop
    (saturatedSheafFunctionEquiv e hq (etaleSourceImage j) t).val = _
  rw [saturatedSheafFunctionEquiv_val, etaleSourceImageMap_appTop j _
    (show ⊤ ≤ j ⁻¹ᵁ (etaleSourceImage j) from fun x _ ↦ ⟨x, rfl⟩)]
  change (U.left.presheaf.map (homOfLE (le_saturateOpen e hq (etaleSourceImage j))).op ≫
    j.appLE (etaleSourceImage j) ⊤ _) _ = _
  rw [Scheme.Hom.map_appLE]
  rfl

/-- The comparison on an explicitly identified original orbit image. -/
def etaleSourceFunctionEquivOn (O : TopologicalSpace.Opens (Orbit e))
    (he : orbitImageOpen e hq (etaleSourceImage j) = O) :
    (invariantSheaf e).obj.obj (op O) ≃+*
      compatibleFunctions (SchemeRelationRestriction.fst p.left q.left j)
        (SchemeRelationRestriction.snd p.left q.left j) := by
  subst O
  exact etaleSourceFunctionEquiv e hq j

/-- Identifying the image preserves the actual scheme pullback of every section. -/
theorem etaleSourceFunctionEquivOn_appLE (O : TopologicalSpace.Opens (Orbit e))
    (he : orbitImageOpen e hq (etaleSourceImage j) = O)
    (t : (invariantSheaf e).obj.obj (op O)) (h : ⊤ ≤ j ⁻¹ᵁ (pullOpen e O).val) :
    (etaleSourceFunctionEquivOn e hq j O he t).val =
      j.appLE _ ⊤ h ((invariantInclusion e).hom.app (op O) t) := by
  subst O
  exact etaleSourceFunctionEquiv_appLE e hq j t h

end FLT.Mazur.RelativeRelationOrbit
