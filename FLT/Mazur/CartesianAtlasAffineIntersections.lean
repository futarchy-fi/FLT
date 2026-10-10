/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCompactOpenAffineLimit

/-!
# Eventual affine intersections in a cartesian atlas

For a finite compatible family of affine chart opens, separatedness of the
limit makes all chart intersections affine at one common refinement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]
  {K : Type v} [Finite K] (U : ∀ i, K → (D.obj i).Opens)
  (hU : ∀ i k, IsAffineOpen (U i k))
  (hcart : ∀ {i j} (f : i ⟶ j) k, D.map f ⁻¹ᵁ U j k = U i k)

include hc hU hcart in
/-- A finite cartesian affine atlas has affine intersections after one refinement. -/
theorem exists_cartesianAtlas_affine_intersections [c.pt.IsSeparated]
    (i : I) (hlim : ∀ k, IsAffineOpen (c.π.app i ⁻¹ᵁ U i k)) :
    ∃ (j : I) (_ : j ⟶ i), ∀ k l, IsAffineOpen (U j k ⊓ U j l) := by
  have hcompact (p : K × K) : IsCompact ((U i p.1 ⊓ U i p.2 : (D.obj i).Opens) :
      Set (D.obj i)) :=
    (quasiSeparatedSpace_iff_forall_affineOpens.mp inferInstance)
      ⟨U i p.1, hU i p.1⟩ ⟨U i p.2, hU i p.2⟩
  have haffine (p : K × K) : IsAffineOpen (c.π.app i ⁻¹ᵁ (U i p.1 ⊓ U i p.2)) := by
    rw [Scheme.Hom.preimage_inf]
    exact @IsAffineOpen.inf c.pt inferInstance _ _ (hlim p.1) (hlim p.2)
  obtain ⟨j, f, hj⟩ := exists_isAffineOpen_preimages_of_finite D c hc i
    (fun p : K × K ↦ U i p.1 ⊓ U i p.2) hcompact haffine
  refine ⟨j, f, fun k l ↦ ?_⟩
  have h := hj (k, l)
  rwa [Scheme.Hom.preimage_inf, hcart f k, hcart f l] at h

end FLT.Mazur.Approximation
