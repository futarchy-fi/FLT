/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStageObstructionSquare
public import FLT.Mazur.FilteredIdealTensorKernel

/-!
# Eventual ideal tests in actual affine base-change stages

The uniform old-obstruction vanishing theorem is applied to the original
filtered ring diagrams. At every later stage whose square is a categorical
pushout, residual flatness proves the entire extended ideal test there.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TensorProduct
namespace FLT.Mazur.Approximation
universe u v w
variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F G : I ⥤ CommRingCat.{u}) (c : Cocone F) (d : Cocone G)
  (hc : IsColimit c) (hd : IsColimit d)
  [PreservesColimit F (forget CommRingCat)]
  [PreservesColimit G (forget CommRingCat)]
  (η : F ⟶ G) (φ : c.pt →+* d.pt)
  (hφ : ∀ i, (d.ι.app i).hom.comp (η.app i).hom = φ.comp (c.ι.app i).hom)

include hc hd hφ in
/-- A flat colimit eventually gives the full ideal test in every later pushout stage. -/
theorem exists_stage_ideal_injective (hflat : φ.Flat)
    (i : I) [IsNoetherianRing (G.obj i)] (J : Ideal (F.obj i)) (hJ : J.FG)
    (hres : let _ := (η.app i).hom.toAlgebra
      Module.Flat ((F.obj i) ⧸ J) (((F.obj i) ⧸ J) ⊗[F.obj i] (G.obj i))) :
    ∃ (j : I) (g : i ⟶ j), ∀ (k : I) (e : j ⟶ k),
      IsPushout (F.map (g ≫ e)) (η.app i) (η.app k) (G.map (g ≫ e)) →
      let _ := (η.app k).hom.toAlgebra
      Function.Injective
        (FCurve.idealTensorInclusion (S := G.obj k) (J.map (F.map (g ≫ e)).hom)) := by
  obtain ⟨j, g, hg⟩ := exists_obstruction_vanishing_stage
    F G c d hc hd η φ hφ hflat i J hJ
  refine ⟨j, g, fun k e hp ↦ ?_⟩
  let _ := (η.app i).hom.toAlgebra
  let _ := (η.app k).hom.toAlgebra
  let _ := hres
  apply AffineStageObstructionSquare.inclusion_injective
    (F.map (g ≫ e)).hom (G.map (g ≫ e)).hom
    (congrArg CommRingCat.Hom.hom (η.naturality (g ≫ e)).symm) hp J
  exact hg k e

end FLT.Mazur.Approximation
