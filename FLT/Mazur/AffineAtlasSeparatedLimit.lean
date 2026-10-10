/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteAffineOpenClosedDescent
public import FLT.Mazur.OpenIntersectionClosedProjection
public import FLT.Mazur.OpenIntersectionRefinement

/-!
# Separatedness descends through a finite affine atlas

At a stage with affine chart intersections, closedness of the limit projection
and separatedness over the original base descend to one common refinement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (g : i ⟶ j), IsClosedImmersion (D.map g)]

include hc in
/-- Affine intersections let separatedness of a closed limit descend to a finite stage. -/
theorem exists_isSeparated_of_affine_intersections (i : I)
    {S : Scheme.{u}} [IsAffine S] (f : D.obj i ⟶ S) [LocallyOfFiniteType f]
    [IsClosedImmersion (c.π.app i)] [IsSeparated (c.π.app i ≫ f)]
    {K : Type v} [Finite K] (U : K → (D.obj i).Opens)
    (hU : TopologicalSpace.IsOpenCover U) (ha : ∀ k, IsAffineOpen (U k))
    (hi : ∀ k l, IsAffineOpen (U k ⊓ U l)) :
    ∃ (j : I) (g : j ⟶ i), IsSeparated (D.map g ≫ f) := by
  let _ (k : K) : IsAffine (U k).toScheme := ha k
  let Y (p : K × K) := pullback ((U p.1).ι ≫ f) ((U p.2).ι ≫ f)
  let _ (p : K × K) : IsAffine (Y p) := inferInstanceAs
    (IsAffine (pullback ((U p.1).ι ≫ f) ((U p.2).ι ≫ f)))
  let t (p : K × K) := openIntersectionProduct f (U p.1) (U p.2)
  obtain ⟨j, g, hg⟩ := exists_isClosedImmersion_on_affineOpens D c hc i
    (fun p : K × K ↦ U p.1 ⊓ U p.2) (fun p ↦ hi p.1 p.2) Y t
    (fun p ↦ isClosedImmersion_restrict_openIntersectionProduct (c.π.app i) f (U p.1) (U p.2))
  refine ⟨j, g, isSeparated_of_openIntersectionProduct (D.map g ≫ f)
    (fun k ↦ D.map g ⁻¹ᵁ U k) (hU.comap (D.map g).base.hom) (fun k l ↦ ?_)⟩
  exact isClosedImmersion_openIntersectionProduct_of_restrict (D.map g) f (U k) (U l)
    (hg (k, l))

end FLT.Mazur.Approximation
