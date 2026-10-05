/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquifiberedSchemeGluing

/-!
# Base change from cartesian gluing charts

Cartesian coefficient squares on the charts of an equifibered diagram
induce a cartesian square on the colimits. We also give the statement for
arbitrary colimit cocones, including the explicit scheme glue data.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {J : Type v} [SmallCategory J] [Small.{u} J] [Quiver.IsThin J]
  {F G : J ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
  [(F ⋙ Scheme.forget).IsLocallyDirected] [(G ⋙ Scheme.forget).IsLocallyDirected]
  (s : F ⟶ G) (hs : s.Equifibered)

include hs in
/-- Cartesian base squares on charts glue to a cartesian square on colimits. -/
theorem equifibered_colimit_baseChange (a : Cocone F) (b : Cocone G) (t : a.pt ⟶ b.pt)
    (h : ∀ i, IsPullback (s.app i) (a.ι.app i) (b.ι.app i) t) :
    IsPullback (colimMap s) (colimit.desc F a) (colimit.desc G b) t := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (Scheme.IsLocallyDirected.openCover G)
  intro i
  let e := (equifibered_colimit_isPullback s hs i).flip.isoPullback
  apply (h i).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [e, Scheme.Cover.pullbackHom]
  · simp [e]
  · simp
  · simp

include hs in
/-- The same base-change criterion for any chosen colimit cocones. -/
theorem equifibered_cocone_baseChange
    {c : Cocone F} {d : Cocone G} (hc : IsColimit c) (hd : IsColimit d)
    (q : c.pt ⟶ d.pt) (a : Cocone F) (b : Cocone G) (t : a.pt ⟶ b.pt)
    (hq : ∀ i, c.ι.app i ≫ q = s.app i ≫ d.ι.app i)
    (h : ∀ i, IsPullback (s.app i) (a.ι.app i) (b.ι.app i) t) :
    IsPullback q (hc.desc a) (hd.desc b) t := by
  let e := (colimit.isColimit F).coconePointUniqueUpToIso hc
  let f := (colimit.isColimit G).coconePointUniqueUpToIso hd
  apply (equifibered_colimit_baseChange s hs a b t h).of_iso e f (Iso.refl _) (Iso.refl _)
  · apply colimit.hom_ext
    intro i
    simp [e, f, hq]
  · apply colimit.hom_ext
    intro i
    simp [e]
  · apply colimit.hom_ext
    intro i
    simp [f]
  · simp

end FLT.Mazur.Approximation
