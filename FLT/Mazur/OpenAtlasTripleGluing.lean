/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing open atlases from full triple routes

Full-domain triple routes with both ambient factorizations give the
rotation maps. Their threefold composite is the identity, so they
construct actual scheme glue data.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u v

variable {ι : Type v} (X : ι → Scheme.{u}) (U : ∀ i, ι → (X i).Opens)
  (e : ∀ i j, (U i j).toScheme ≅ (U j i).toScheme)
  (r : ∀ i j k, pullback (U i j).ι (U i k).ι ⟶ (U j k).toScheme)
  (hf : ∀ i j k, r i j k ≫ (U j k).ι =
    pullback.fst _ _ ≫ (e i j).hom ≫ (U j i).ι)

/-- Rotate the entire ambient triple intersection using its constructed route. -/
def openAtlasTripleRotate (i j k : ι) :
    pullback (U i j).ι (U i k).ι ⟶ pullback (U j k).ι (U j i).ι :=
  pullback.lift (r i j k) (pullback.fst _ _ ≫ (e i j).hom) (hf i j k)

/-- The first projection of a rotation is the prescribed full-domain triple route. -/
@[reassoc (attr := simp)] theorem openAtlasTripleRotate_fst (i j k : ι) :
    openAtlasTripleRotate X U e r hf i j k ≫ pullback.fst _ _ = r i j k :=
  pullback.lift_fst _ _ _

/-- The second projection is the pair comparison on the full first overlap. -/
@[reassoc (attr := simp)] theorem openAtlasTripleRotate_snd (i j k : ι) :
    openAtlasTripleRotate X U e r hf i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ (e i j).hom := pullback.lift_snd _ _ _

variable
  (hc : ∀ i j k, r i j k ≫ (e j k).hom ≫ (U k j).ι =
    pullback.snd _ _ ≫ (e i k).hom ≫ (U k i).ι)
  (he : ∀ i j, (e i j).hom ≫ (e j i).hom = 𝟙 _)

include hc he in
/-- Full ambient factorization equations prove the full threefold rotation cocycle. -/
theorem openAtlasTripleRotate_cocycle (i j k : ι) :
    openAtlasTripleRotate X U e r hf i j k ≫ openAtlasTripleRotate X U e r hf j k i ≫
        openAtlasTripleRotate X U e r hf k i j = 𝟙 _ := by
  apply (cancel_mono (pullback.fst (U i j).ι (U i k).ι ≫ (U i j).ι)).mp
  simp only [Category.assoc, openAtlasTripleRotate_fst_assoc, hf,
    openAtlasTripleRotate_fst_assoc, hc, openAtlasTripleRotate_snd_assoc]
  rw [← Category.assoc (e i j).hom, he, Category.id_comp, Category.id_comp]

variable [Small.{u} ι] (hU : ∀ i, U i i = ⊤) (hi : ∀ i, (e i i).hom = 𝟙 _)

/-- Whole diagonals and the proved full cocycle assemble actual scheme glue data. -/
def openAtlasTripleGlueData : Scheme.GlueData.{u} where
  J := Shrink.{u} ι
  U i := X ((equivShrink ι).symm i)
  V p := (U ((equivShrink ι).symm p.1) ((equivShrink ι).symm p.2)).toScheme
  f i j := (U ((equivShrink ι).symm i) ((equivShrink ι).symm j)).ι
  f_id i := by
    rw [hU]
    exact (X ((equivShrink ι).symm i)).topIso.isIso_hom
  t i j := (e ((equivShrink ι).symm i) ((equivShrink ι).symm j)).hom
  t_id i := hi _
  t' i j k := openAtlasTripleRotate X U e r hf
    ((equivShrink ι).symm i) ((equivShrink ι).symm j) ((equivShrink ι).symm k)
  t_fac i j k := openAtlasTripleRotate_snd X U e r hf _ _ _
  cocycle i j k := openAtlasTripleRotate_cocycle X U e r hf hc he _ _ _
  f_open _ := inferInstance

end FLT.Mazur
