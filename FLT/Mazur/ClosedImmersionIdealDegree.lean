/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedImmersionIdealCorrespondence
public import FLT.Mazur.ConstantDegree

/-!
# Finite locally free families in a closed ambient scheme

The full ideal correspondence preserves the actual closed family over any
base. Thus finite locally free degree is equivalent on the two sides, with
no basis, chosen isomorphism, or degree conclusion supplied as extra input.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (p : Y ⟶ S)

/-- Closed ambient pushforward has the same actual family, via its image isomorphism. -/
def closedIdealFamilyIso (J : X.IdealSheafData) :
    Over.mk (J.subschemeι ≫ i ≫ p) ≅ Over.mk ((J.map i).subschemeι ≫ p) := by
  refine Over.isoMk (asIso (J.subschemeι ≫ i).toImage) ?_
  change (J.subschemeι ≫ i).toImage ≫ (J.subschemeι ≫ i).imageι ≫ p = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc]
  rfl

/-- The exact degree property is preserved by the full closed ambient ideal correspondence. -/
theorem closedIdeal_degree_iff (J : X.IdealSheafData) (d : ℕ) :
    FiniteLocallyFreeDegree (J.subschemeι ≫ i ≫ p) d ↔
      FiniteLocallyFreeDegree ((J.map i).subschemeι ≫ p) d :=
  finiteLocallyFreeDegree_iff_of_overIso (closedIdealFamilyIso i p J)

/-- Finite locally free families in the closed ambient scheme are exactly containing families. -/
def closedIdealFamilyEquiv (d : ℕ) :
    { J : X.IdealSheafData // FiniteLocallyFreeDegree (J.subschemeι ≫ i ≫ p) d } ≃
      { J : Y.IdealSheafData // i.ker ≤ J ∧
        FiniteLocallyFreeDegree (J.subschemeι ≫ p) d } where
  toFun J := ⟨J.val.map i, Scheme.Hom.le_ker_comp _ _,
    (closedIdeal_degree_iff i p J.val d).mp J.property⟩
  invFun J := ⟨J.val.comap i, (closedIdeal_degree_iff i p (J.val.comap i) d).mpr (by
    rw [closed_map_comap i J.val J.property.1]
    exact J.property.2)⟩
  left_inv J := Subtype.ext (closed_comap_map i J.val)
  right_inv J := Subtype.ext (closed_map_comap i J.val J.property.1)

end FLT.Mazur.ClosedIdealCover
