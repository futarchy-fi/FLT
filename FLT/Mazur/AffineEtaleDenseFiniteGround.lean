/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SpecGenericFiniteOpen
public import FLT.Mazur.AffineEtaleTranslationFiniteBranch

/-!
# Dense original coefficient opens with finite entire translations

Apply generic freeness to the actual section algebra of an affine etale
translation over a domain. Its entire Cartesian pullback becomes finite over
one dense principal open in the ORIGINAL coefficient scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineEtaleDenseFiniteGround
open Approximation
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R] [IsDomain R]
  (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
local notation "B" => affineBaseSections R V
local instance : Algebra.Etale R B := EtaleTranslationBranch.sectionAlgebra_etale V.hom

/-- A constructed original coefficient, independent of the chosen envelope source or open. -/
def coefficient : R := SpecGenericFlatOpen.coefficient R B

theorem coefficient_ne_zero : coefficient R V ≠ 0 :=
  SpecGenericFlatOpen.coefficient_ne_zero R B

/-- The entire principal coefficient open, with its original structural map. -/
def groundMap : Spec (.of (Localization.Away (coefficient R V))) ⟶ Spec (.of R) :=
  SpecGenericFlatOpen.targetMap R B

instance groundMap_isOpenImmersion : IsOpenImmersion (groundMap R V) :=
  inferInstanceAs (IsOpenImmersion (SpecGenericFlatOpen.targetMap R B))

instance groundMap_isDominant : IsDominant (groundMap R V) :=
  inferInstanceAs (IsDominant (SpecGenericFlatOpen.targetMap R B))

/-- Every original translation branch survives in the finite changed translation. -/
instance translation_isFinite : IsFinite (pullback.snd V.hom (groundMap R V)) := by
  let q := groundMap R V
  let p := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hp : V.left.isoSpec.hom ≫ p = V.hom := affineBaseSectionsSpecIso_over R V
  let m := pullback.map V.hom q p q V.left.isoSpec.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; exact hp.symm) (by simp only [Category.id_comp,
      Category.comp_id])
  let _ : IsIso m := inferInstanceAs (IsIso (pullback.map _ _ _ _ _ _ _ _ _))
  let _ : IsFinite (pullback.fst q p) :=
    inferInstanceAs (IsFinite (SpecGenericFlatOpen.projection R B))
  have hf : IsFinite (pullback.snd p q) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    infer_instance
  let _ := hf
  have hm : m ≫ pullback.snd p q = pullback.snd V.hom q := by
    simp only [m, pullback.map, pullback.lift_snd, Category.comp_id]
  change IsFinite (pullback.snd V.hom q)
  rw [← hm]
  infer_instance

end FLT.Mazur.AffineEtaleDenseFiniteGround
