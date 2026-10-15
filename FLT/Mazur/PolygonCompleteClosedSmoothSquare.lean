/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonCompleteClosedSmoothLocus
public import FLT.Mazur.PolygonSmoothFiniteAtlas

/-!
# The actual smooth closed-fiber square of the complete polygon

Restrict the original cartesian closed fiber to its smooth open. The square
keeps the actual closed inclusion and the constant-coefficient base map.
Its finite Laurent charts are the original normalization charts.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeClosedFiberInclusion
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "π" => exactVeroneseProjToBase K n h
local notation "c" => PolygonCyclicAtlas.toBase K n h
local notation "j" => completeClosedFiberInclusion K n h

/-- The original closed inclusion restricted to the whole smooth polygon. -/
def completeClosedSmoothInclusion : (c).smoothLocus.toScheme ⟶ (π).smoothLocus.toScheme :=
  IsOpenImmersion.lift (π).smoothLocus.ι ((c).smoothLocus.ι ≫ (j)) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact (completeClosedFiber_mem_smoothLocus K n h x.1).mpr x.2)

/-- Restriction retains the original complete-family closed inclusion. -/
@[reassoc] theorem completeClosedSmoothInclusion_inclusion :
    completeClosedSmoothInclusion K n h ≫ (π).smoothLocus.ι =
      (c).smoothLocus.ι ≫ (j) := IsOpenImmersion.lift_fac _ _ _

/-- The original smooth restriction square is cartesian. -/
theorem completeClosedSmoothInclusion_open_isPullback :
    IsPullback (completeClosedSmoothInclusion K n h) (c).smoothLocus.ι
      (π).smoothLocus.ι (j) := by
  apply IsOpenImmersion.isPullback
  · exact (completeClosedSmoothInclusion_inclusion K n h).symm
  · rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι,
      completeClosedFiber_preimage_smoothLocus]

/-- The smooth polygon is the actual base change of the complete relative smooth scheme. -/
theorem completeClosedSmoothInclusion_isPullback :
    IsPullback (completeClosedSmoothInclusion K n h) ((c).smoothLocus.ι ≫ c)
      ((π).smoothLocus.ι ≫ π) (completeClosedBase K) :=
  (completeClosedSmoothInclusion_open_isPullback K n h).paste_vert
    (completeClosedFiber_isPullback K n h)

/-- The restricted inclusion keeps the actual constant-coefficient base map. -/
@[reassoc] theorem completeClosedSmoothInclusion_structure :
    completeClosedSmoothInclusion K n h ≫ (π).smoothLocus.ι ≫ π =
      (c).smoothLocus.ι ≫ c ≫ completeClosedBase K := by
  simpa only [Category.assoc] using (completeClosedSmoothInclusion_isPullback K n h).w

/-- The whole smooth closed polygon is isomorphic to the actual smooth fiber product. -/
def completeClosedSmoothFiberIso : (c).smoothLocus.toScheme ≅
    pullback ((π).smoothLocus.ι ≫ π) (completeClosedBase K) :=
  (completeClosedSmoothInclusion_isPullback K n h).isoPullback

/-- The comparison to the fiber product preserves the actual smooth inclusion. -/
@[reassoc] theorem completeClosedSmoothFiberIso_fst :
    (completeClosedSmoothFiberIso K n h).hom ≫ pullback.fst _ _ =
      completeClosedSmoothInclusion K n h :=
  (completeClosedSmoothInclusion_isPullback K n h).isoPullback_hom_fst

/-- The comparison to the fiber product preserves its residue-field projection. -/
@[reassoc] theorem completeClosedSmoothFiberIso_snd :
    (completeClosedSmoothFiberIso K n h).hom ≫ pullback.snd _ _ =
      (c).smoothLocus.ι ≫ c :=
  (completeClosedSmoothInclusion_isPullback K n h).isoPullback_hom_snd

end FLT.Mazur.PolygonInfinitesimalStages
