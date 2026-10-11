/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFlatFamilyReflection
public import FLT.Mazur.RelativeCartierIdealFamilyDescent
public import FLT.Mazur.RelativeCartier

/-!
# Flatness descent for full closed divisors

The comap of a full ideal defines the actual fiber product closed subscheme.
The induced fppf cover of that subscheme detects flatness over the original
base. Applied to relative total spaces this supplies the missing relative
flatness condition from the original flat local divisors.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open SchemePicard
variable {X S : Scheme.{0}}

/-- Full closed-subscheme flatness descends along an arbitrary fppf ambient cover. -/
theorem flat_fullDivisor_of_fppf_comaps (f : X ⟶ S) (I : X.IdealSheafData)
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage X)
    (h : ∀ i, Flat ((I.comap (C.f i)).subschemeι ≫ C.f i ≫ f)) :
    Flat (I.subschemeι ≫ f) := by
  apply SchemeFlatFamilyReflection.flat_of_fppf_cover _ (C.pullback₂ I.subschemeι)
  intro i
  let _ := h i
  change Flat (pullback.snd (C.f i) I.subschemeι ≫ I.subschemeι ≫ f)
  have he : pullback.snd (C.f i) I.subschemeι ≫ I.subschemeι ≫ f =
      (I.comapIso (C.f i)).inv ≫ ((I.comap (C.f i)).subschemeι ≫ C.f i ≫ f) := by
    rw [← Category.assoc, ← Category.assoc, I.comapIso_inv_subschemeι,
      pullback.condition_assoc, Category.assoc]
  rw [he]
  infer_instance

/-- Flatness over the test base follows from flatness of every original relative comap. -/
theorem flat_relativeFullDivisor_of_cover (f : X ⟶ S) (T : Over S)
    (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
    (I : (pullback f T.hom).IdealSheafData)
    (h : ∀ i, Flat ((I.comap (relativeTotalMap f (relativeCoverArrow T 𝒰 i))).subschemeι ≫
      pullback.snd f (relativeCoverMember T 𝒰 i).hom)) :
    Flat (I.subschemeι ≫ pullback.snd f T.hom) := by
  apply flat_fullDivisor_of_fppf_comaps _ I (relativeTotalCover f T 𝒰)
  intro i
  let _ : Flat (relativeCoverArrow T 𝒰 i).left :=
    (Scheme.Cover.map_prop (P := @Flat ⊓ @LocallyOfFinitePresentation) 𝒰 i).1
  let _ := h i
  change Flat ((I.comap (relativeTotalMap f (relativeCoverArrow T 𝒰 i))).subschemeι ≫
    relativeTotalMap f (relativeCoverArrow T 𝒰 i) ≫ pullback.snd f T.hom)
  rw [relativeTotalMap_snd, ← Category.assoc]
  infer_instance

/-- Relative full Cartier ideals descend effectively on arbitrary fppf test covers. -/
theorem existsUnique_relativeEffectiveCartier_family_descent (f : X ⟶ S) (T : Over S)
    (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
    (I : ∀ i, (pullback f (relativeCoverMember T 𝒰 i).hom).IdealSheafData)
    (hI : ∀ i, RelativeEffectiveCartier (pullback.snd f (relativeCoverMember T 𝒰 i).hom)
      (I i))
    (h : ∀ i j, (I i).comap (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j)) =
      (I j).comap (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))) :
    ∃! J : (pullback f T.hom).IdealSheafData,
      RelativeEffectiveCartier (pullback.snd f T.hom) J ∧
        ∀ i, J.comap (relativeTotalMap f (relativeCoverArrow T 𝒰 i)) = I i := by
  obtain ⟨J, hJ, hu⟩ := existsUnique_relativeCartierIdeal_family_descent f T 𝒰 I
    (fun i ↦ (hI i).1) h
  refine ⟨J, ⟨⟨hJ.1, ?_⟩, hJ.2⟩, fun K hK ↦ hu K ⟨hK.1.1, hK.2⟩⟩
  apply flat_relativeFullDivisor_of_cover f T 𝒰 J
  intro i
  rw [hJ.2 i]
  exact (hI i).2

end FLT.Mazur.FCurve
