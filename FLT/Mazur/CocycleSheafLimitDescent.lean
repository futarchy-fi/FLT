/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntersectionCocycleLimitUnits
public import FLT.Mazur.IntersectionCocyclePullbackRecovery

/-!
# Gluing a descended cocycle sheaf at a finite stage

The transition units constructed from the limit cocycle glue to a genuine
line sheaf at a common refinement. Its actual pullback is the original sheaf.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- A cocycle on the limit charts descends to a line sheaf with actual pullback recovery. -/
theorem exists_cocycleSheaf_of_limit {ι : Type u} [Finite ι]
    (i : I) (U : ι → (D.obj i).Opens) (hcover : iSup U = ⊤)
    (hcompact : ∀ s, IsCompact (finiteIntersectionOpen U s : Set (D.obj i)))
    (g : Cocycle (fun j ↦ c.π.app i ⁻¹ᵁ U j)) :
    ∃ (r : Over i) (M : (D.obj r.left).Modules), LocallyFreeRankOne M ∧
      Nonempty ((Scheme.Modules.pullback (c.π.app r.left)).obj M ≅ g.sheaf) := by
  obtain ⟨r, y, hy, hnat, hmul⟩ :=
    exists_intersectionCocycle_limit_units D c hc i U hcompact g
  let O (s : NonemptyChartSet ι) := D.map r.hom ⁻¹ᵁ finiteIntersectionOpen U s
  have hanti : Antitone O := fun _ _ h ↦
    (D.map r.hom).preimage_mono (finiteIntersectionOpen_antitone U h)
  have hunion s t : O (unionChartSet s t) = O s ⊓ O t := by
    dsimp [O]
    rw [finiteIntersectionOpen_union, Scheme.Hom.preimage_inf]
  have hcov : (⨆ j, O (singletonChartSet j)) = ⊤ := by
    simp only [O, finiteIntersectionOpen_singleton]
    exact (D.map r.hom).iSup_preimage_eq_top hcover
  let G := intersectionUnitsCocycle O hanti hunion y hnat hmul
  have hproj (s) : c.π.app r.left ⁻¹ᵁ O s =
      c.π.app i ⁻¹ᵁ finiteIntersectionOpen U s := by
    change c.π.app r.left ⁻¹ᵁ D.map r.hom ⁻¹ᵁ _ = _
    rw [← Scheme.Hom.comp_preimage, c.w]
  have hU j : c.π.app r.left ⁻¹ᵁ O (singletonChartSet j) = c.π.app i ⁻¹ᵁ U j := by
    rw [hproj, finiteIntersectionOpen_singleton]
  refine ⟨r, G.sheaf, G.locallyFreeRankOne hcov, ⟨?_⟩⟩
  apply intersectionUnitsCocyclePullbackIso O hanti hunion y hnat hmul
    (c.π.app r.left) g hU _ hcov
  intro j k
  apply Units.ext
  let s := pairChartSet j k
  let p : IntersectionPair s := (⟨j, by simp [s]⟩, ⟨k, by simp [s]⟩)
  have he := congrArg (fun z : Γ(c.pt, c.π.app i ⁻¹ᵁ finiteIntersectionOpen U s) ↦
    res (hproj s).le z) (congrArg Units.val (hy s p))
  change res _ ((c.π.app r.left).appLE _ _ _ (y s p).val) = _ at he
  have hres : (c.π.app r.left).appLE (O s)
      (c.π.app i ⁻¹ᵁ finiteIntersectionOpen U s) (hproj s).symm.le ≫
        c.pt.presheaf.map (homOfLE (hproj s).le).op = (c.π.app r.left).app (O s) := by
    exact ((c.π.app r.left).appLE_map (hproj s).symm.le
      (homOfLE (hproj s).le).op).trans (c.π.app r.left).appLE_eq_app
  have heq := congrArg (fun q : Γ(D.obj r.left, O s) ⟶
      Γ(c.pt, c.π.app r.left ⁻¹ᵁ O s) ↦ q (y s p).val) hres
  exact heq.symm.trans (he.trans (g.natural _ _ _ _ _))

end FLT.Mazur.Approximation
