/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedIdealCartesianDegree

/-!
# Actual finite locally free ideal families in an arbitrary ambient

Use the actual scheme pullback of an ambient over its base. Full ideal
families have only a degree property as input. Their arbitrary base change
is literal ideal pullback along a constructed cartesian ambient map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.ClosedIdealCover

variable {A S X Y Z : Scheme.{u}} (a : A ⟶ S) (d : ℕ)
variable (s : X ⟶ S) (t : Y ⟶ S)

/-- All actual full ideals of finite locally free degree in the ambient base change. -/
def RelativeIdealFamilies :=
  { J : (pullback s a).IdealSheafData //
    FiniteLocallyFreeDegree (J.subschemeι ≫ pullback.fst s a) d }

/-- The actual ambient map induced by a map of scheme bases. -/
def relativeIdealAmbientMap (g : Y ⟶ X) (hg : g ≫ s = t) : pullback t a ⟶ pullback s a :=
  pullback.lift (pullback.fst _ _ ≫ g) (pullback.snd _ _) (by
    rw [Category.assoc, hg]
    exact pullback.condition)

/-- The induced ambient map retains the base-change projection. -/
@[reassoc]
theorem relativeIdealAmbientMap_fst (g : Y ⟶ X) (hg : g ≫ s = t) :
    relativeIdealAmbientMap a s t g hg ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g :=
  pullback.lift_fst _ _ _

/-- The induced ambient map retains the original ambient projection. -/
@[reassoc]
theorem relativeIdealAmbientMap_snd (g : Y ⟶ X) (hg : g ≫ s = t) :
    relativeIdealAmbientMap a s t g hg ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The constructed ambient square is cartesian over every map of scheme bases. -/
theorem relativeIdealAmbientMap_isPullback (g : Y ⟶ X) (hg : g ≫ s = t) :
    IsPullback (relativeIdealAmbientMap a s t g hg) (pullback.fst _ _) (pullback.fst _ _) g := by
  have h : IsPullback (pullback.fst t a)
      (relativeIdealAmbientMap a s t g hg ≫ pullback.snd _ _) (g ≫ s) a := by
    rw [relativeIdealAmbientMap_snd, hg]
    exact IsPullback.of_hasPullback _ _
  exact (h.of_bot (relativeIdealAmbientMap_fst a s t g hg).symm
    (IsPullback.of_hasPullback _ _)).flip

/-- Actual full-ideal pullback preserves the degree by the constructed cartesian square. -/
def relativeIdealFamilyBaseChange (g : Y ⟶ X) (hg : g ≫ s = t)
    (J : RelativeIdealFamilies a d s) : RelativeIdealFamilies a d t :=
  ⟨J.val.comap (relativeIdealAmbientMap a s t g hg),
    restriction_degree J.val _ (relativeIdealAmbientMap_isPullback a s t g hg) d J.property⟩

/-- The actual relative ambient identity is the identity morphism. -/
theorem relativeIdealAmbientMap_id :
    relativeIdealAmbientMap a s s (𝟙 X) (Category.id_comp s) = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [relativeIdealAmbientMap_fst, relativeIdealAmbientMap_snd,
      Category.id_comp, Category.comp_id]

/-- Actual relative ambient maps compose along composition of scheme bases. -/
theorem relativeIdealAmbientMap_comp (r : Z ⟶ S) (g : Y ⟶ X) (hg : g ≫ s = t)
    (h : Z ⟶ Y) (hh : h ≫ t = r) :
    relativeIdealAmbientMap a t r h hh ≫ relativeIdealAmbientMap a s t g hg =
      relativeIdealAmbientMap a s r (h ≫ g) (by rw [Category.assoc, hg, hh]) := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, relativeIdealAmbientMap_fst,
      relativeIdealAmbientMap_snd, relativeIdealAmbientMap_fst_assoc]

/-- Pullback along the identity fixes the whole family ideal. -/
theorem relativeIdealFamilyBaseChange_id (J : RelativeIdealFamilies a d s) :
    relativeIdealFamilyBaseChange a d s s (𝟙 X) (Category.id_comp s) J = J := by
  apply Subtype.ext
  change J.val.comap _ = J.val
  rw [relativeIdealAmbientMap_id, comap_id]

/-- Iterated arbitrary base change agrees with pullback along the composite on full ideals. -/
theorem relativeIdealFamilyBaseChange_comp (r : Z ⟶ S) (g : Y ⟶ X) (hg : g ≫ s = t)
    (h : Z ⟶ Y) (hh : h ≫ t = r) (J : RelativeIdealFamilies a d s) :
    relativeIdealFamilyBaseChange a d t r h hh (relativeIdealFamilyBaseChange a d s t g hg J) =
      relativeIdealFamilyBaseChange a d s r (h ≫ g) (by rw [Category.assoc, hg, hh]) J := by
  apply Subtype.ext
  change (J.val.comap _).comap _ = J.val.comap _
  rw [← comap_comp, relativeIdealAmbientMap_comp]

end FLT.Mazur.ClosedIdealCover
