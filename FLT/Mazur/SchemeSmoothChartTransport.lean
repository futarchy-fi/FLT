/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# Transport of exact smooth chart covers

Seal smooth-locus and image bookkeeping before substituting recursive models.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.SchemeSmoothChartTransport
variable {U V T X Y S : Scheme}

/-- A structure-preserving isomorphism preserves the exact smooth point set. -/
theorem mem_smooth_iff (e : X ≅ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    (h : e.hom ≫ q = p) (x : X) :
    e.hom x ∈ q.smoothLocus.carrier ↔ x ∈ p.smoothLocus.carrier := by
  subst p
  exact PolygonAtlas.mem_smooth_iff e.hom q x

/-- An exact two-chart smooth cover transports along a structure-preserving isomorphism. -/
theorem cover (a : U ⟶ X) (b : V ⟶ X) (g : T ⟶ X) (e : X ≅ Y)
    (p : X ⟶ S) (q : Y ⟶ S)
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    (h : e.hom ≫ q = p)
    (hc : Set.range a ∪ Set.range b = Set.range g ∩ p.smoothLocus.carrier) :
    Set.range (a ≫ e.hom) ∪ Set.range (b ≫ e.hom) =
      Set.range (g ≫ e.hom) ∩ q.smoothLocus.carrier := by
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [← Set.image_union, hc]
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (mem_smooth_iff e p q h x).mpr hx'⟩
  · rintro ⟨⟨x, hx, rfl⟩, hx'⟩
    exact ⟨x, ⟨hx, (mem_smooth_iff e p q h x).mp hx'⟩, rfl⟩

end FLT.Mazur.SchemeSmoothChartTransport
