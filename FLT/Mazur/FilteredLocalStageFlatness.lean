/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredIdealTensorKernel
public import FLT.Mazur.LocalMaximalStageCriterion

/-!
# Eventual flatness of local Noetherian pushout stages

Uniform vanishing in the original filtered diagrams combines with the actual
stage square and the local maximal-ideal criterion. The resulting stage is flat,
not merely a stage at which the old obstruction map vanishes. The local and
pushout hypotheses remain explicit for application to chosen geometric points.
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
/-- Every later local Noetherian pushout stage with local base transition is flat. -/
theorem exists_local_stage_flat (hflat : φ.Flat) (i : I)
    [IsLocalRing (F.obj i)] [IsNoetherianRing (F.obj i)] [IsNoetherianRing (G.obj i)] :
    ∃ (j : I) (g : i ⟶ j), ∀ (k : I) (e : j ⟶ k),
      ∀ [IsLocalRing (F.obj k)] [IsNoetherianRing (F.obj k)]
        [IsLocalRing (G.obj k)] [IsNoetherianRing (G.obj k)]
        [IsLocalHom (F.map (g ≫ e)).hom] [IsLocalHom (η.app k).hom],
      IsPushout (F.map (g ≫ e)) (η.app i) (η.app k) (G.map (g ≫ e)) →
      let _ := (η.app k).hom.toAlgebra
      Module.Flat (F.obj k) (G.obj k) := by
  obtain ⟨j, g, hg⟩ := exists_obstruction_vanishing_stage
    F G c d hc hd η φ hφ hflat i (IsLocalRing.maximalIdeal (F.obj i))
    (IsNoetherian.noetherian _)
  refine ⟨j, g, fun k e _ _ _ _ _ _ hp ↦ ?_⟩
  let _ := (η.app i).hom.toAlgebra
  let _ := (η.app k).hom.toAlgebra
  apply LocalMaximalStageCriterion.flat (F.map (g ≫ e)).hom (G.map (g ≫ e)).hom
    (congrArg CommRingCat.Hom.hom (η.naturality (g ≫ e)).symm) hp (G.obj k)
  exact hg k e

include hc hd hφ in
/-- The same single stage works for every later local target localization of a pushout. -/
theorem exists_localized_stage_flat (hflat : φ.Flat) (i : I)
    [IsLocalRing (F.obj i)] [IsNoetherianRing (F.obj i)] [IsNoetherianRing (G.obj i)] :
    ∃ (j : I) (g : i ⟶ j), ∀ (k : I) (e : j ⟶ k),
      ∀ [IsLocalRing (F.obj k)] [IsNoetherianRing (F.obj k)]
        [IsLocalHom (F.map (g ≫ e)).hom],
      IsPushout (F.map (g ≫ e)) (η.app i) (η.app k) (G.map (g ≫ e)) →
      let _ := (η.app k).hom.toAlgebra
      ∀ (T : Type u) [CommRing T] [Algebra (F.obj k) T] [Algebra (G.obj k) T]
        [IsScalarTower (F.obj k) (G.obj k) T] [IsLocalRing T] [IsNoetherianRing T]
        [IsLocalHom (algebraMap (F.obj k) T)]
        (U : Submonoid (G.obj k)) [IsLocalization U T], Module.Flat (F.obj k) T := by
  obtain ⟨j, g, hg⟩ := exists_obstruction_vanishing_stage
    F G c d hc hd η φ hφ hflat i (IsLocalRing.maximalIdeal (F.obj i))
    (IsNoetherian.noetherian _)
  refine ⟨j, g, fun k e _ _ _ hp T _ _ _ _ _ _ _ U _ ↦ ?_⟩
  let _ := (η.app i).hom.toAlgebra
  let _ := (η.app k).hom.toAlgebra
  apply LocalMaximalStageCriterion.localization_flat
    (F.map (g ≫ e)).hom (G.map (g ≫ e)).hom
    (congrArg CommRingCat.Hom.hom (η.naturality (g ≫ e)).symm) hp T U
  exact hg k e

end FLT.Mazur.Approximation
