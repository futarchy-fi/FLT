/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalCoefficientTransport
public import FLT.Mazur.PolygonInfinitesimalSpecialFiber
public import FLT.Mazur.PolygonCyclicPushout

/-!
# Every field-valued fiber is the original cyclic polygon

A field kills the actual nilpotent smoothing parameter. The complete coefficient
pullback therefore identifies every field fiber, including any chosen cartesian
square, with the original polygon and its specified pinching cocone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (L : Type u) [Field L] (f : R →+* L) (n : ℕ) (h : 2 ≤ n)

/-- Every field-valued coefficient map kills the nilpotent smoothing parameter. -/
theorem fieldParameter_zero : f t = 0 :=
  ((Fact.out : IsNilpotent t).map f).eq_zero

/-- The original cyclic polygon is the actual fiber along any field-valued ring map. -/
def fieldFiberIso : PolygonCyclicAtlas.scheme L n h ≅
    pullback (toBase R t n h) (Spec.map (CommRingCat.ofHom f)) :=
  zeroFiberIso L n h ≪≫ parameterPullbackIso f t 0 (fieldParameter_zero R t L f) n h

/-- The field-fiber comparison retains the original polygon's coefficient map. -/
@[reassoc] theorem fieldFiberIso_snd :
    (fieldFiberIso R t L f n h).hom ≫ pullback.snd _ _ =
      PolygonCyclicAtlas.toBase L n h := by
  rw [fieldFiberIso, Iso.trans_hom, Category.assoc, parameterPullbackIso_snd,
    zeroFiberIso_base]

/-- The field-fiber comparison retains the actual coefficient inclusion from every node. -/
@[reassoc] theorem chart_fieldFiberIso_fst (i : Fin n) :
    PolygonCyclicAtlas.chart L n h i ≫ (fieldFiberIso R t L f n h).hom ≫
      pullback.fst _ _ =
        (PolygonSmoothing.specialFiberIso L).hom ≫ chart L 0 n h i ≫
          parameterProjection f t 0 (fieldParameter_zero R t L f) n h := by
  rw [fieldFiberIso, Iso.trans_hom, Category.assoc, parameterPullbackIso_fst,
    chart_zeroFiberIso_assoc]

variable (s : Spec (.of L) ⟶ Spec (.of R))

/-- The constructed field-point comparison, together with its proved base equality. -/
def pointFiberComparison :
    {e : PolygonCyclicAtlas.scheme L n h ≅ pullback (toBase R t n h) s //
      e.hom ≫ pullback.snd _ _ = PolygonCyclicAtlas.toBase L n h} := by
  have e : {e : PolygonCyclicAtlas.scheme L n h ≅
      pullback (toBase R t n h) (Spec.map (CommRingCat.ofHom (Spec.preimage s).hom)) //
      e.hom ≫ pullback.snd _ _ = PolygonCyclicAtlas.toBase L n h} :=
    ⟨fieldFiberIso R t L (Spec.preimage s).hom n h,
      fieldFiberIso_snd R t L (Spec.preimage s).hom n h⟩
  rw [show Spec.map (CommRingCat.ofHom (Spec.preimage s).hom) = s from
    Spec.map_preimage s] at e
  exact e

/-- The comparison also applies to an arbitrary scheme-valued field point. -/
def pointFiberIso : PolygonCyclicAtlas.scheme L n h ≅ pullback (toBase R t n h) s :=
  (pointFiberComparison R t L n h s).val

/-- The field-point comparison retains the original polygon structure map. -/
@[reassoc] theorem pointFiberIso_snd :
    (pointFiberIso R t L n h s).hom ≫ pullback.snd _ _ =
      PolygonCyclicAtlas.toBase L n h :=
  (pointFiberComparison R t L n h s).property

/-- Every chosen field-fiber square has the specified cyclic polygon pinching presentation. -/
theorem fieldFiber_exists_cocone {Y : Scheme.{u}} (p : Y ⟶ scheme R t n h)
    (q : Y ⟶ Spec (.of L)) (hp : IsPullback p q (toBase R t n h) s) :
    ∃ (a : PolygonPinching.components L n ⟶ Over.mk q)
      (b : PolygonPinching.nodes L n ⟶ Over.mk q),
      IsPushout (PolygonPinching.toComponents L n (by omega))
        (PolygonPinching.toNodes L n) a b := by
  let e : PolygonCyclicAtlas.polygon L n h ≅ Over.mk q :=
    Over.isoMk (pointFiberIso R t L n h s ≪≫ hp.isoPullback.symm) (by
      change ((pointFiberIso R t L n h s).hom ≫ hp.isoPullback.inv) ≫ q =
        PolygonCyclicAtlas.toBase L n h
      rw [Category.assoc, IsPullback.isoPullback_inv_snd, pointFiberIso_snd])
  exact ⟨PolygonCyclicAtlas.normalization L n h ≫ e.hom,
    PolygonCyclicAtlas.nodes L n h ≫ e.hom,
    (PolygonCyclicPushout.isPushout L n h (by omega)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (by simp) (by simp)⟩

end FLT.Mazur.PolygonInfinitesimal
