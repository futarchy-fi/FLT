/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationRestrictionRechart
public import FLT.Mazur.RelativeRelationSaturatedSheafImage

/-!
# Effective invariant function descent for arbitrary open source immersions

An open source immersion is identified with its actual image. Full-relation
function descent then uses the original geometric pullback on that source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y X : Scheme.{u}} (k : Y ⟶ X) [IsOpenImmersion k]

/-- An open source is canonically its actual image in the original scheme. -/
def openSourceIso : Y ≅ k.opensRange.toScheme :=
  IsOpenImmersion.isoOfRangeEq k k.opensRange.ι (by rw [Scheme.Opens.range_ι]; rfl)

@[reassoc]
theorem openSourceIso_hom : (openSourceIso k).hom ≫ k.opensRange.ι = k :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Image coordinates compute exactly the original pullback of an open section. -/
theorem openSourceIso_appTop (v : Γ(X, k.opensRange))
    (h : ⊤ ≤ k ⁻¹ᵁ k.opensRange) :
    (openSourceIso k).hom.appTop (k.opensRange.topIso.inv v) =
      k.appLE k.opensRange ⊤ h v := by
  have ht : k.opensRange.topIso.inv =
      k.opensRange.ι.appLE k.opensRange ⊤ k.opensRange.ι_preimage_self.ge := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
    congr 1
  rw [ht]
  have hc := Scheme.Hom.appLE_comp_appLE (openSourceIso k).hom k.opensRange.ι
    k.opensRange ⊤ ⊤ k.opensRange.ι_preimage_self.ge le_rfl
  have he : (openSourceIso k).hom.appLE ⊤ ⊤ le_rfl =
      (openSourceIso k).hom.appTop := by simp [Scheme.Hom.appLE]
  simp only [openSourceIso_hom, he] at hc
  exact congrArg (fun g ↦ g v) hc

variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  {T : Scheme.{u}} (j : T ⟶ U.left) [IsOpenImmersion j] [Etale q.left]

/-- Original quotient sections on the image are the full compatible functions on the open source. -/
def openSourceFunctionEquiv :
    (invariantSheaf e).obj.obj (op (orbitImageOpen e hq j.opensRange)) ≃+*
      compatibleFunctions (SchemeRelationRestriction.fst p.left q.left j)
        (SchemeRelationRestriction.snd p.left q.left j) :=
  (saturatedSheafFunctionEquiv e hq j.opensRange).trans
    (SchemeRelationRestriction.sourceIsoEquiv p.left q.left j j.opensRange.ι
      (openSourceIso j) (openSourceIso_hom j))

/-- The comparison preserves the original restriction and image-coordinate maps. -/
theorem openSourceFunctionEquiv_val
    (t : (invariantSheaf e).obj.obj (op (orbitImageOpen e hq j.opensRange))) :
    (openSourceFunctionEquiv e hq j t).val =
      (openSourceIso j).hom.appTop (j.opensRange.topIso.inv
        (saturatedSheafRestriction e hq j.opensRange t)) := by
  change (openSourceIso j).hom.appTop
    (saturatedSheafFunctionEquiv e hq j.opensRange t).val = _
  rw [saturatedSheafFunctionEquiv_val]

/-- In original coordinates the comparison is the source immersion's actual pullback. -/
theorem openSourceFunctionEquiv_appLE
    (t : (invariantSheaf e).obj.obj (op (orbitImageOpen e hq j.opensRange)))
    (h : ⊤ ≤ j ⁻¹ᵁ (pullOpen e (orbitImageOpen e hq j.opensRange)).val) :
    (openSourceFunctionEquiv e hq j t).val =
      j.appLE _ ⊤ h
        ((invariantInclusion e).hom.app (op (orbitImageOpen e hq j.opensRange)) t) := by
  rw [openSourceFunctionEquiv_val, openSourceIso_appTop j _
    (show ⊤ ≤ j ⁻¹ᵁ j.opensRange from fun x _ ↦ ⟨x, rfl⟩)]
  change (U.left.presheaf.map (homOfLE (le_saturateOpen e hq j.opensRange)).op ≫
    j.appLE j.opensRange ⊤ _) _ = _
  rw [Scheme.Hom.map_appLE]
  rfl

/-- Descent through an open source with its exact quotient image explicitly identified. -/
def openSourceFunctionEquivOn (O : TopologicalSpace.Opens (Orbit e))
    (he : orbitImageOpen e hq j.opensRange = O) :
    (invariantSheaf e).obj.obj (op O) ≃+*
      compatibleFunctions (SchemeRelationRestriction.fst p.left q.left j)
        (SchemeRelationRestriction.snd p.left q.left j) := by
  subst O
  exact openSourceFunctionEquiv e hq j

/-- The identified-domain comparison still uses the original source pullback. -/
theorem openSourceFunctionEquivOn_appLE (O : TopologicalSpace.Opens (Orbit e))
    (he : orbitImageOpen e hq j.opensRange = O)
    (t : (invariantSheaf e).obj.obj (op O)) (h : ⊤ ≤ j ⁻¹ᵁ (pullOpen e O).val) :
    (openSourceFunctionEquivOn e hq j O he t).val =
      j.appLE _ ⊤ h ((invariantInclusion e).hom.app (op O) t) := by
  subst O
  exact openSourceFunctionEquiv_appLE e hq j t h

end FLT.Mazur.RelativeRelationOrbit
