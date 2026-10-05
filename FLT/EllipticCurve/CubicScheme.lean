/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCharts

/-!
# The Weierstrass scheme glued from two affine charts

Glue the ordinary equation at Z=1 to the infinity equation at Y=1 using
the explicit isomorphism of their overlap rings. The construction supplies
a scheme over the coefficient base, a two-chart open cover and an infinity
section. Properness, the projective embedding, and the group law remain
separate theorems; this is not a construction of a modular curve.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeierstrassCurve.CubicCharts

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The affine spectrum of a chart ring. -/
abbrev chart (b : Bool) : Scheme.{u} := Spec (.of (Ring W b))

/-- The principal open immersion from the localized chart ring. -/
def overlapInclusion (b : Bool) : Spec (.of (Overlap W b)) ⟶ chart W b :=
  Spec.map (CommRingCat.ofHom (algebraMap (Ring W b) (Overlap W b)))

instance overlapInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (overlapInclusion W b) :=
  IsOpenImmersion.of_isLocalization (coord W b 1)

/-- The isomorphism of the overlap schemes, oriented from the ordinary chart. -/
def overlapIso : Spec (.of (Overlap W false)) ≅ Spec (.of (Overlap W true)) :=
  Scheme.Spec.mapIso (overlapEquiv W).symm.toRingEquiv.toCommRingCatIso.op

theorem overlapIso_hom :
    (overlapIso W).hom = Spec.map (CommRingCat.ofHom (transition W false).toRingHom) := rfl

/-- The overlap inclusion into the infinity chart after changing coordinates. -/
def overlapRight : Spec (.of (Overlap W false)) ⟶ chart W true :=
  (overlapIso W).hom ≫ overlapInclusion W true

instance overlapRight_isOpenImmersion : IsOpenImmersion (overlapRight W) := by
  unfold overlapRight
  infer_instance

/-- The actual scheme obtained by gluing the two charts along their overlap. -/
def scheme : Scheme.{u} := pushout (overlapInclusion W false) (overlapRight W)

/-- The ordinary affine chart of the glued scheme. -/
def affineChart : chart W false ⟶ scheme W := pushout.inl _ _
/-- The infinity chart of the glued scheme. -/
def infinityChart : chart W true ⟶ scheme W := pushout.inr _ _

instance affineChart_isOpenImmersion : IsOpenImmersion (affineChart W) := by
  change IsOpenImmersion (colimit.ι (span (overlapInclusion W false) (overlapRight W))
    WalkingSpan.left)
  infer_instance

instance infinityChart_isOpenImmersion : IsOpenImmersion (infinityChart W) := by
  change IsOpenImmersion (colimit.ι (span (overlapInclusion W false) (overlapRight W))
    WalkingSpan.right)
  infer_instance

theorem overlap_condition :
    overlapInclusion W false ≫ affineChart W = overlapRight W ≫ infinityChart W :=
  pushout.condition

/-- The coefficient-base projection of either affine chart. -/
def chartToBase (b : Bool) : chart W b ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Ring W b)))

theorem overlap_toBase :
    overlapInclusion W false ≫ chartToBase W false =
      overlapRight W ≫ chartToBase W true := by
  unfold overlapRight
  rw [Category.assoc, overlapIso_hom]
  unfold overlapInclusion chartToBase
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  change algebraMap (Ring W false) (Overlap W false) (algebraMap R (Ring W false) r) =
    transition W false
      (algebraMap (Ring W true) (Overlap W true) (algebraMap R (Ring W true) r))
  rw [← IsScalarTower.algebraMap_apply R (Ring W false),
    ← IsScalarTower.algebraMap_apply R (Ring W true)]
  exact ((transition W false).commutes r).symm

/-- Projection of the glued scheme to the coefficient base. -/
def toBase : scheme W ⟶ Spec (.of R) :=
  pushout.desc (chartToBase W false) (chartToBase W true) (overlap_toBase W)

@[reassoc (attr := simp)] theorem affineChart_toBase :
    affineChart W ≫ toBase W = chartToBase W false := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem infinityChart_toBase :
    infinityChart W ≫ toBase W = chartToBase W true := pushout.inr_desc _ _ _

/-- The original infinity section, now in the glued scheme. -/
def infinity : Spec (.of R) ⟶ scheme W :=
  InfinityChart.infinity W ≫ infinityChart W

@[reassoc (attr := simp)] theorem infinity_toBase :
    infinity W ≫ toBase W = 𝟙 _ := by
  unfold infinity
  erw [Category.assoc, infinityChart_toBase]
  exact InfinityChart.infinity_toBase W

/-- The two genuine open charts cover every scheme point. -/
theorem charts_cover (x : scheme W) :
    (∃ y : chart W false, affineChart W y = x) ∨
      ∃ y : chart W true, infinityChart W y = x := by
  obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (overlapInclusion W false) (overlapRight W)) x
  cases i with
  | none =>
    left
    refine ⟨overlapInclusion W false y, ?_⟩
    change (overlapInclusion W false ≫ affineChart W) y = x
    rw [show overlapInclusion W false ≫ affineChart W =
      colimit.ι (span (overlapInclusion W false) (overlapRight W)) WalkingSpan.zero from
        colimit.w (span (overlapInclusion W false) (overlapRight W)) WalkingSpan.Hom.fst]
    exact hy
  | some i =>
    cases i with
    | left => exact Or.inl ⟨y, hy⟩
    | right => exact Or.inr ⟨y, hy⟩

end WeierstrassCurve.CubicCharts
