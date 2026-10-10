/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineClosedLimitDescent
public import FLT.Mazur.OpenRestrictionLimitMap

/-!
# Closed immersion descent on a prescribed affine open

An affine open of one stage and its finite-type map to an affine target
are kept fixed. If the induced limit map is closed, its restriction along
one later transition is closed as well.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsClosedImmersion (D.map f)]

include hc in
/-- Closedness of a map on a fixed affine open descends through the original transitions. -/
theorem exists_isClosedImmersion_on_affineOpen (i : I) (U : (D.obj i).Opens)
    (hU : IsAffineOpen U) {Y : Scheme.{u}} [IsAffine Y] (g : U.toScheme ⟶ Y)
    [LocallyOfFiniteType g] (h : IsClosedImmersion ((c.π.app i ∣_ U) ≫ g)) :
    ∃ (j : I) (f : j ⟶ i), IsClosedImmersion ((D.map f ∣_ U) ≫ g) := by
  let _ {j k : I} (f : j ⟶ k) : IsAffineHom (D.map f) := inferInstance
  let _ (j : Over i) : IsAffine ((opensDiagram D i U).obj j) :=
    hU.preimage (D.map j.hom)
  let _ {j k : Over i} (f : j ⟶ k) :
      IsClosedImmersion ((opensDiagram D i U).map f) :=
    opensDiagram_map_isClosedImmersion D i U f
  let t := opensDiagramToOpen D i U ≫ (Functor.const (Over i)).map g
  let q : (opensCone D c i U).pt ⟶ Y := (c.π.app i ∣_ U) ≫ g
  let _ : IsClosedImmersion q := h
  have hq (j : Over i) : (opensCone D c i U).π.app j ≫ t.app j = q :=
    opensCone_toOpen_assoc D i U c j g
  let _ : LocallyOfFiniteType (t.app (Over.mk (𝟙 i))) :=
    inferInstanceAs (LocallyOfFiniteType ((D.map (𝟙 i) ∣_ U) ≫ g))
  obtain ⟨j, _, hj⟩ := exists_isClosedImmersion_of_affine_limit (opensDiagram D i U)
    (opensCone D c i U) (isLimitOpensCone D c hc i U) t q hq (Over.mk (𝟙 i))
  exact ⟨j.left, j.hom, hj⟩

end FLT.Mazur.Approximation
