/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionGluingSections
public import FLT.Mazur.IntersectionUnitCocycle
public import FLT.Mazur.ModuleSheafUnitCocycleRestrict

/-!
# The invertible sheaf on a glued affine intersection model

Transport the coordinate units to actual ambient sections. Their naturality
and multiplication equations construct a cocycle on the singleton open cover,
and hence a genuine locally free rank-one module sheaf on the model colimit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

variable {S : Type u} [CommRing S] {ι : Type u} [Finite ι]
  (C : NonemptyChartSet ι ⥤ CommAlgCat S)
  [∀ a b (f : a ⟶ b), IsOpenImmersion (Spec.map (CommRingCat.ofHom (C.map f).hom.toRingHom))]
  [((affineIntersectionSchemeDiagram C) ⋙ Scheme.forget).IsLocallyDirected]
  (y : ∀ s, IntersectionPair s → (C.obj s)ˣ)
  (hnat : ∀ {s t} (f : s ⟶ t) (k : IntersectionPair s),
    (C.map f).hom (y s k) = (y t (intersectionPairMap f k) : C.obj t))
  (hmul : ∀ s (k : IntersectionTriple s),
    y s (k.1, k.2.1) * y s (k.2.1, k.2.2) = y s (k.1, k.2.2))

/-- The coordinate transition unit as an actual ambient unit on the model. -/
def affineIntersectionAmbientUnit (s : NonemptyChartSet ι) (k : IntersectionPair s) :
    Γ(colimit (affineIntersectionSchemeDiagram C),
      intersectionColimitOpen (affineIntersectionSchemeDiagram C) s)ˣ :=
  Units.map (affineIntersectionColimitSectionEquiv C s).toMonoidHom (y s k)

include hnat in
/-- Ambient transition units respect inclusion of intersection charts. -/
theorem affineIntersectionAmbientUnit_naturality {s t : NonemptyChartSet ι}
    (h : s ≤ t) (k : IntersectionPair s) :
    res (intersectionColimitOpen_antitone (affineIntersectionSchemeDiagram C) h)
        (affineIntersectionAmbientUnit C y s k :
          Γ(colimit (affineIntersectionSchemeDiagram C),
            intersectionColimitOpen (affineIntersectionSchemeDiagram C) s)) =
      (affineIntersectionAmbientUnit C y t (intersectionPairMap (homOfLE h) k) :
        Γ(colimit (affineIntersectionSchemeDiagram C),
          intersectionColimitOpen (affineIntersectionSchemeDiagram C) t)) := by
  change res _ (affineIntersectionColimitSectionEquiv C s _) =
    affineIntersectionColimitSectionEquiv C t _
  rw [show res _ (affineIntersectionColimitSectionEquiv C s (y s k)) = _ from
    affineIntersectionColimitSectionEquiv_naturality C h (y s k), hnat]

include hmul in
/-- The coordinate multiplication equations survive transport to ambient units. -/
theorem affineIntersectionAmbientUnit_mul (s : NonemptyChartSet ι)
    (k : IntersectionTriple s) :
    affineIntersectionAmbientUnit C y s (k.1, k.2.1) *
      affineIntersectionAmbientUnit C y s (k.2.1, k.2.2) =
        affineIntersectionAmbientUnit C y s (k.1, k.2.2) := by
  unfold affineIntersectionAmbientUnit
  rw [← map_mul, hmul]

/-- The descended unit data define a genuine cocycle on the model scheme. -/
def affineIntersectionModelCocycle :
    Cocycle (fun i ↦ intersectionColimitOpen (affineIntersectionSchemeDiagram C)
      (singletonChartSet i)) :=
  intersectionUnitsCocycle (intersectionColimitOpen (affineIntersectionSchemeDiagram C))
    (intersectionColimitOpen_antitone _) (intersectionColimitOpen_union _)
    (affineIntersectionAmbientUnit C y) (affineIntersectionAmbientUnit_naturality C y hnat)
    (affineIntersectionAmbientUnit_mul C y hmul)

/-- On any smaller intersection, the model transition is the specified coordinate unit. -/
theorem affineIntersectionModelCocycle_unit_eq (i j : ι)
    (V : (colimit (affineIntersectionSchemeDiagram C)).Opens)
    (hi : V ≤ intersectionColimitOpen (affineIntersectionSchemeDiagram C) (singletonChartSet i))
    (hj : V ≤ intersectionColimitOpen (affineIntersectionSchemeDiagram C) (singletonChartSet j))
    (s : NonemptyChartSet ι) (his : i ∈ s.val) (hjs : j ∈ s.val)
    (hV : V ≤ intersectionColimitOpen (affineIntersectionSchemeDiagram C) s) :
    (affineIntersectionModelCocycle C y hnat hmul).unit i j V hi hj =
      Units.map (affineIntersectionSectionToOpen C s V hV).toMonoidHom
        (y s (⟨i, his⟩, ⟨j, hjs⟩)) := by
  change singletonTransitionUnit _ (intersectionColimitOpen_union _)
    (affineIntersectionAmbientUnit C y) i j V hi hj = _
  rw [singletonTransitionUnit_eq _ (intersectionColimitOpen_antitone _)
    (intersectionColimitOpen_union _) _
    (affineIntersectionAmbientUnit_naturality C y hnat) i j V hi hj s his hjs hV]
  apply Units.ext
  rfl

/-- The actual module sheaf defined by the descended transitions. -/
def affineIntersectionModelSheaf :
    (colimit (affineIntersectionSchemeDiagram C)).Modules :=
  (affineIntersectionModelCocycle C y hnat hmul).sheaf

/-- Singleton chart evaluation trivializes the model sheaf. -/
def affineIntersectionModelSheafChartIso (i : ι) :
    (affineIntersectionModelSheaf C y hnat hmul).restrict
        (intersectionColimitOpen (affineIntersectionSchemeDiagram C) (singletonChartSet i)).ι ≅
      structureModule
        (intersectionColimitOpen (affineIntersectionSchemeDiagram C)
          (singletonChartSet i)).toScheme :=
  (affineIntersectionModelCocycle C y hnat hmul).restrictIso i

/-- The constructed sheaf is locally free of rank one on the model. -/
theorem affineIntersectionModelSheaf_rankOne :
    LocallyFreeRankOne (affineIntersectionModelSheaf C y hnat hmul) :=
  (affineIntersectionModelCocycle C y hnat hmul).locallyFreeRankOne
    (intersectionColimitOpen_singleton_cover (affineIntersectionSchemeDiagram C))

end FLT.Mazur.Approximation
