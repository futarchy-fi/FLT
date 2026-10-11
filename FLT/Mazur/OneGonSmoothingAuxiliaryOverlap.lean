/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingUniversalComparison
public import FLT.Mazur.UniversalWeierstrassAuxiliaryEtale

/-!
# An actual etale auxiliary overlap on the smooth one-gon boundary

Pull back the existing surjective etale level-four parameter scheme along
the original boundary coefficient point. This constructs the overlap and
its local supply of auxiliary markings without assuming a chosen global
basis on the punctured complete base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))

/-- The actual overlap of the smooth boundary with the original auxiliary scheme. -/
def smoothAuxiliaryOverlap : Scheme :=
  pullback levelFour.hom (Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)))

/-- The retained auxiliary family on the overlap. -/
def smoothAuxiliaryPoint : smoothAuxiliaryOverlap t h₂ ht hf ⟶ levelFour.left :=
  pullback.fst _ _

/-- The overlap's original boundary coefficient projection. -/
def smoothAuxiliaryProjection : smoothAuxiliaryOverlap t h₂ ht hf ⟶ Spec (.of R) :=
  pullback.snd _ _

/-- The auxiliary point keeps the original one-gon coefficient parameter. -/
@[reassoc] theorem smoothAuxiliaryPoint_base :
    smoothAuxiliaryPoint t h₂ ht hf ≫ levelFour.hom =
      smoothAuxiliaryProjection t h₂ ht hf ≫
        Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf)) :=
  pullback.condition

/-- The overlap is etale over the actual boundary base. -/
instance smoothAuxiliaryProjection_etale : Etale (smoothAuxiliaryProjection t h₂ ht hf) := by
  unfold smoothAuxiliaryProjection
  infer_instance

/-- Auxiliary markings exist locally on the entire original smooth boundary base. -/
instance smoothAuxiliaryProjection_surjective :
    Surjective (smoothAuxiliaryProjection t h₂ ht hf) := by
  unfold smoothAuxiliaryProjection
  infer_instance

/-- The actual auxiliary overlap is a single-member etale covering family. -/
def smoothAuxiliaryCover : (Spec (.of R)).Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers Unit (fun _ => smoothAuxiliaryOverlap t h₂ ht hf)
    (fun _ => smoothAuxiliaryProjection t h₂ ht hf)
    (fun s ↦ by
      obtain ⟨x, hx⟩ := (smoothAuxiliaryProjection t h₂ ht hf).surjective s
      exact ⟨(), x, hx⟩)

/-- A specified auxiliary boundary point lifts to the actual overlap. -/
def smoothAuxiliaryLift {T : Scheme} (f : T ⟶ levelFour.left) (b : T ⟶ Spec (.of R))
    (hb : f ≫ levelFour.hom =
      b ≫ Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf))) :
    T ⟶ smoothAuxiliaryOverlap t h₂ ht hf :=
  pullback.lift f b hb

/-- The overlap lift retains the original full auxiliary point. -/
@[reassoc] theorem smoothAuxiliaryLift_point {T : Scheme}
    (f : T ⟶ levelFour.left) (b : T ⟶ Spec (.of R))
    (hb : f ≫ levelFour.hom =
      b ≫ Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf))) :
    smoothAuxiliaryLift t h₂ ht hf f b hb ≫ smoothAuxiliaryPoint t h₂ ht hf = f :=
  pullback.lift_fst _ _ _

/-- The overlap lift retains the original boundary projection. -/
@[reassoc] theorem smoothAuxiliaryLift_projection {T : Scheme}
    (f : T ⟶ levelFour.left) (b : T ⟶ Spec (.of R))
    (hb : f ≫ levelFour.hom =
      b ≫ Spec.map (CommRingCat.ofHom (smoothParameter t h₂ ht hf))) :
    smoothAuxiliaryLift t h₂ ht hf f b hb ≫ smoothAuxiliaryProjection t h₂ ht hf = b :=
  pullback.lift_snd _ _ _

end FLT.Mazur.OneGonSmoothing
