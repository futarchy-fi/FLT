/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionIdealCorrespondence
public import FLT.Mazur.ConstantDegree

/-!
# Finite locally free families across ambient opens

Extension and restriction identify all finite locally free ideal families in
an ambient open with the families in the separated ambient whose entire
support lies in that open. Both directions preserve the actual family over
the base, hence its rank including multiplicities.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.OpenIdealCover

set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] (p : Y ⟶ S)

/-- Extension of a closed open family retains the actual family over the base. -/
def openIdealFamilyIso (J : X.IdealSheafData) [IsClosedImmersion (J.subschemeι ≫ i)] :
    Over.mk (J.subschemeι ≫ i ≫ p) ≅ Over.mk ((J.map i).subschemeι ≫ p) := by
  refine Over.isoMk (asIso (J.subschemeι ≫ i).toImage) ?_
  change (J.subschemeι ≫ i).toImage ≫ (J.subschemeι ≫ i).imageι ≫ p = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc]
  rfl

/-- A supported closed family is unchanged as a scheme over the base by open restriction. -/
def supportedIdealFamilyIso (J : Y.IdealSheafData)
    (h : Set.range J.subschemeι ⊆ Set.range i) :
    Over.mk ((J.comap i).subschemeι ≫ i ≫ p) ≅ Over.mk (J.subschemeι ≫ p) := by
  let f := IsOpenImmersion.lift i J.subschemeι h
  have hf : f ≫ i = J.subschemeι := IsOpenImmersion.lift_fac _ _ _
  let q : IsPullback f (𝟙 J.subscheme) i J.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨hf.trans (Category.id_comp _).symm⟩
  refine Over.isoMk (J.comapIso i ≪≫ q.isoPullback.symm) ?_
  change (J.comapIso i).hom ≫ q.isoPullback.inv ≫ J.subschemeι ≫ p = _
  have he : q.isoPullback.inv ≫ J.subschemeι = pullback.fst i J.subschemeι ≫ i := by
    calc
      _ = q.isoPullback.inv ≫ f ≫ i := by rw [hf]
      _ = _ := q.isoPullback_inv_fst_assoc i
  rw [← Category.assoc q.isoPullback.inv, he, Category.assoc,
    ← Category.assoc (J.comapIso i).hom, comapIso_hom_fst]
  rfl

/-- Actual finite locally free open families correspond exactly to supported ambient families. -/
def openIdealFamilyEquiv [IsSeparated p] (d : ℕ) :
    { J : X.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ i ≫ p) d } ≃
      { J : Y.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ p) d ∧
        Set.range J.subschemeι ⊆ Set.range i } where
  toFun J := by
    let _ := J.property.1
    let _ := finiteFamily_closed i p J.val
    exact ⟨J.val.map i, J.property.of_overIso (openIdealFamilyIso i p J.val),
      open_map_range i J.val⟩
  invFun J := ⟨J.val.comap i,
    J.property.1.of_overIso (supportedIdealFamilyIso i p J.val J.property.2).symm⟩
  left_inv J := by
    let _ := J.property.1
    let _ := finiteFamily_closed i p J.val
    exact Subtype.ext (open_comap_map i J.val)
  right_inv J := Subtype.ext (open_map_comap i J.val J.property.2)

/-- The equivalence extends the full original ideal, not just its reduced support. -/
theorem openIdealFamilyEquiv_ideal [IsSeparated p] (d : ℕ)
    (J : { J : X.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ i ≫ p) d }) :
    (openIdealFamilyEquiv i p d J).val = J.val.map i := rfl

end FLT.Mazur.OpenIdealCover
