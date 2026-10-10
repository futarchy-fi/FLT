/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntersectionSectionGluing

/-!
# Actual global cocycle sections descend through inverse limits

For a fixed finite-stage line cocycle, descend the coordinates of finitely
many specified global sections and glue them at one refinement. Recovery
uses the actual cone pullback maps on every chart intersection.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Specified global sections descend to actual global sections with exact coordinate recovery. -/
theorem exists_cocycleGlobalSections_of_limit {ι T : Type u} [Finite ι] [Finite T]
    (i : I) (U : ι → (D.obj i).Opens)
    (hcompact : ∀ s, IsCompact (finiteIntersectionOpen U s : Set (D.obj i)))
    (g : Cocycle U) (σ : T → (g.inverseImage (c.π.app i)).sections ⊤) :
    ∃ (r : Over i) (τ : T → (g.inverseImage (D.map r.hom)).sections ⊤),
      ∀ l s (k : {j // j ∈ s.val}), (c.π.app r.left).appLE _ _
        (by rw [← Scheme.Hom.comp_preimage, c.w])
        ((g.inverseImage (D.map r.hom)).globalCoordinate (τ l) k.val
          (D.map r.hom ⁻¹ᵁ finiteIntersectionOpen U s)
          ((D.map r.hom).preimage_mono (finiteIntersectionOpen_le_chart U s k))) =
        (g.inverseImage (c.π.app i)).globalCoordinate (σ l) k.val _
          ((c.π.app i).preimage_mono (finiteIntersectionOpen_le_chart U s k)) := by
  obtain ⟨r, y, hy, hnat, htrans⟩ :=
    exists_intersectionSection_limit_coordinates D c hc i U hcompact g σ
  let O (s : NonemptyChartSet ι) := D.map r.hom ⁻¹ᵁ finiteIntersectionOpen U s
  have hanti : Antitone O := fun _ _ h ↦
    (D.map r.hom).preimage_mono (finiteIntersectionOpen_antitone U h)
  have hunion s t : O (unionChartSet s t) = O s ⊓ O t := by
    dsimp [O]
    rw [finiteIntersectionOpen_union, Scheme.Hom.preimage_inf]
  have hsingle j : O (singletonChartSet j) = D.map r.hom ⁻¹ᵁ U j := by
    simp only [O, finiteIntersectionOpen_singleton]
  let G := g.inverseImage (D.map r.hom)
  have hG s (k : IntersectionPair s) l : y s (k.1, l) =
      (G.unit k.1.val k.2.val (O s)
        ((hanti (singletonChartSet_le_of_mem k.1)).trans (hsingle k.1.val).le)
        ((hanti (singletonChartSet_le_of_mem k.2)).trans (hsingle k.2.val).le) :
          Γ(D.obj r.left, O s)) * y s (k.2, l) := by
    rw [htrans]
    congr 1
    simpa only [G, Cocycle.inverseImage, Scheme.Hom.app_eq_appLE] using
      (g.inverseImageUnit_eq (D.map r.hom) k.1.val k.2.val _
        ((hanti (singletonChartSet_le_of_mem k.1)).trans (hsingle k.1.val).le)
        ((hanti (singletonChartSet_le_of_mem k.2)).trans (hsingle k.2.val).le)
        (finiteIntersectionOpen U s) (finiteIntersectionOpen_le_chart U s k.1)
        (finiteIntersectionOpen_le_chart U s k.2) le_rfl).symm
  obtain ⟨τ, hτ⟩ := exists_globalSection_of_intersection_coordinates O hanti hunion
    y hnat hsingle G hG
  refine ⟨r, τ, fun l s k ↦ ?_⟩
  rw [hτ]
  exact hy s (k, l)

end FLT.Mazur.Approximation
