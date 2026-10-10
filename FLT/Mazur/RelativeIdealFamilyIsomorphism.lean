/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealFamilies
public import FLT.Mazur.IdealFamilyIsomorphism

/-!
# Natural transport of intrinsic families under an ambient isomorphism

An isomorphism of original ambient schemes over the coefficient base induces
actual isomorphisms of every scheme pullback. Transport of full ideal families
along these isomorphisms commutes with arbitrary base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.ClosedIdealCover

variable {A B S X Y : Scheme.{u}} (e : A ≅ B) (a : A ⟶ S) (b : B ⟶ S)
variable (he : e.hom ≫ b = a) (s : X ⟶ S)

/-- An actual ambient isomorphism induces the actual isomorphism of its scheme base changes. -/
def relativeIdealAmbientIso : pullback s a ≅ pullback s b where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e.hom) (by
    rw [Category.assoc, he]
    exact pullback.condition)
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e.inv) (by
    rw [← he, Category.assoc, e.inv_hom_id_assoc]
    exact pullback.condition)
  hom_inv_id := by
    apply pullback.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [Category.assoc]

/-- Ambient isomorphism transport retains the actual test-scheme projection. -/
@[reassoc]
theorem relativeIdealAmbientIso_hom_fst :
    (relativeIdealAmbientIso e a b he s).hom ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- Ambient isomorphism transport acts by the given map on the original ambient projection. -/
@[reassoc]
theorem relativeIdealAmbientIso_hom_snd :
    (relativeIdealAmbientIso e a b he s).hom ≫ pullback.snd _ _ = pullback.snd _ _ ≫ e.hom :=
  pullback.lift_snd _ _ _

/-- All intrinsic full ideal families transport across the given original ambient isomorphism. -/
def relativeIdealFamilyIsoEquiv (d : ℕ) :
    RelativeIdealFamilies a d s ≃ RelativeIdealFamilies b d s :=
  idealFamilyIsoEquiv (relativeIdealAmbientIso e a b he s) _ _
    (relativeIdealAmbientIso_hom_fst e a b he s) d

variable (t : Y ⟶ S) (g : Y ⟶ X) (hg : g ≫ s = t)

/-- The actual ambient pullback isomorphisms commute with every morphism of test schemes. -/
theorem relativeIdealAmbientIso_natural :
    (relativeIdealAmbientIso e a b he t).hom ≫ relativeIdealAmbientMap b s t g hg =
      relativeIdealAmbientMap a s t g hg ≫ (relativeIdealAmbientIso e a b he s).hom := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, relativeIdealAmbientMap_fst, relativeIdealAmbientMap_snd,
      relativeIdealAmbientIso_hom_fst, relativeIdealAmbientIso_hom_snd,
      relativeIdealAmbientIso_hom_fst_assoc, relativeIdealAmbientMap_snd_assoc]

/-- Transport of complete family ideals commutes with arbitrary scheme base change. -/
theorem relativeIdealFamilyIsoEquiv_natural (d : ℕ) (J : RelativeIdealFamilies a d s) :
    relativeIdealFamilyIsoEquiv e a b he t d (relativeIdealFamilyBaseChange a d s t g hg J) =
      relativeIdealFamilyBaseChange b d s t g hg (relativeIdealFamilyIsoEquiv e a b he s d J) := by
  apply Subtype.ext
  exact idealFamilyIso_comap (relativeIdealAmbientIso e a b he s)
    (relativeIdealAmbientIso e a b he t) _ _
    (relativeIdealAmbientIso_natural e a b he s t g hg) J.val

end FLT.Mazur.ClosedIdealCover
