/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenClosedLimitDescent

/-!
# Simultaneous closedness on finitely many affine opens

Finitely many maps from prescribed affine opens to affine targets become
closed immersions at one common refinement when they are closed on the limit.
This retains the original opens and targets throughout the construction.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsClosedImmersion (D.map f)]

include hc in
/-- Closedness of finitely many maps on affine opens occurs at one common stage. -/
theorem exists_isClosedImmersion_on_affineOpens {K : Type v} [Finite K]
    (i : I) (U : K → (D.obj i).Opens) (hU : ∀ k, IsAffineOpen (U k))
    (Y : K → Scheme.{u}) [∀ k, IsAffine (Y k)]
    (g : ∀ k, (U k).toScheme ⟶ Y k) [∀ k, LocallyOfFiniteType (g k)]
    (h : ∀ k, IsClosedImmersion ((c.π.app i ∣_ U k) ≫ g k)) :
    ∃ (j : I) (f : j ⟶ i), ∀ k, IsClosedImmersion ((D.map f ∣_ U k) ≫ g k) := by
  classical
  choose j f hj using fun k ↦
    exists_isClosedImmersion_on_affineOpen D c hc i (U k) (hU k) (g k) (h k)
  cases nonempty_fintype K
  let A (k : K) : Over i := Over.mk (f k)
  obtain ⟨B, hB⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image A)
  refine ⟨B.left, B.hom, fun k ↦ ?_⟩
  let r : B ⟶ A k := (hB (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)).some
  let t := opensDiagramToOpen D i (U k) ≫ (Functor.const (Over i)).map (g k)
  let _ : IsClosedImmersion (t.app (A k)) := hj k
  let _ : IsClosedImmersion ((opensDiagram D i (U k)).map r) :=
    opensDiagram_map_isClosedImmersion D i (U k) r
  have he : (opensDiagram D i (U k)).map r ≫ t.app (A k) = t.app B :=
    (t.naturality r).trans (Category.comp_id _)
  exact (congrArg (fun z ↦ IsClosedImmersion z) he).mp
    (inferInstanceAs (IsClosedImmersion ((opensDiagram D i (U k)).map r ≫ t.app (A k))))

end FLT.Mazur.Approximation
