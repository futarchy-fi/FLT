/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineBundlePullback
public import FLT.Mazur.ModuleSheafOpenImageChart

/-!
# Detecting line bundles on open-immersion covers

A trivialization on an open chart transfers to its image. Local rank-one
trivializations on a covering family therefore give local rank one globally.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.FCurve
open ModuleSheafOpenImageChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {M : X.Modules}

/-- A trivialization along an open immersion gives a trivialization on its image. -/
def imageTrivialization (i : Y ⟶ X) [IsOpenImmersion i]
    (e : M.restrict i ≅ structureModule Y) :
    M.restrict i.opensRange.ι ≅ structureModule i.opensRange.toScheme := by
  have h : (imageIso i).inv ≫ i = i.opensRange.ι := by
    apply (cancel_epi (imageIso i).hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, imageIso_hom_ι]
  exact (restrictFunctorCongr h).symm.app M ≪≫
    (restrictFunctorComp (imageIso i).inv i).app M ≪≫
    (restrictFunctor (imageIso i).inv).mapIso e ≪≫ restrictUnitIso (imageIso i).inv

/-- Local rank one is detected on any jointly covering family of open immersions. -/
theorem LocallyFreeRankOne.of_openImmersionCover {ι : Type v}
    (Y : ι → Scheme.{u}) (i : ∀ k, Y k ⟶ X) [∀ k, IsOpenImmersion (i k)]
    (hcover : ∀ x : X, ∃ k, x ∈ Set.range (i k))
    (hM : ∀ k, LocallyFreeRankOne (M.restrict (i k))) : LocallyFreeRankOne M := by
  intro x
  obtain ⟨k, y, rfl⟩ := hcover x
  obtain ⟨V, hy, ⟨e⟩⟩ := hM k y
  let j := V.ι ≫ i k
  refine ⟨j.opensRange, ?_, ⟨imageTrivialization j
    ((restrictFunctorComp V.ι (i k)).app M ≪≫ e)⟩⟩
  exact ⟨⟨y, hy⟩, rfl⟩

/-- The actual pullbacks to an open-immersion cover also detect local rank one. -/
theorem LocallyFreeRankOne.of_openPullbackCover {ι : Type v}
    (Y : ι → Scheme.{u}) (i : ∀ k, Y k ⟶ X) [∀ k, IsOpenImmersion (i k)]
    (hcover : ∀ x : X, ∃ k, x ∈ Set.range (i k))
    (hM : ∀ k, LocallyFreeRankOne ((Scheme.Modules.pullback (i k)).obj M)) : LocallyFreeRankOne M :=
  .of_openImmersionCover Y i hcover
    (fun k ↦ (hM k).of_iso ((restrictFunctorIsoPullback (i k)).app M).symm)

end FLT.Mazur.FCurve
