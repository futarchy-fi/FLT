/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePushforwardCohomology

/-!
# Boundaries after restriction to an affine open

The restriction adjunction maps the actual coefficient sheaf into the direct
image of its restriction. Affine direct-image cohomology and affine vanishing
show that every positive-degree cocycle becomes a boundary there. Thus the
bounding cochain lives on the intersections of the original cover with the
open, without choosing a comparison between two independently built Ext maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve.AffineOpenCechBoundary

open CechSheafHZero

variable {X : Scheme.{u}} [X.IsSeparated] (W : X.Opens) (hW : IsAffineOpen W)
  (M : X.Modules) [M.IsQuasicoherent]

/-- Coefficients whose sections are the original sections restricted to the open. -/
abbrev coefficients : X.Modules := (pushforward W.ι).obj (M.restrict W.ι)

/-- The actual section-restriction morphism, given by the restriction adjunction. -/
def restriction : M ⟶ coefficients W M := (restrictAdjunction W.ι).unit.app M

omit [X.IsSeparated] [M.IsQuasicoherent] in
/-- The adjunction map is ordinary restriction on every ambient open. -/
lemma restriction_app (V : X.Opens) :
    (restriction W M).app V =
      M.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op := rfl

include hW in
/-- Direct image of the restricted module has zero positive cohomology. -/
theorem coefficients_cohomology_subsingleton (q : ℕ) (hq : 0 < q) :
    Subsingleton (ModuleH (coefficients W M) q) := by
  let : IsAffine W.toScheme := hW
  have : IsAffineHom (W.ι ≫ terminal.from X) := by
    rw [terminal.comp_from]
    infer_instance
  have : IsAffineHom W.ι := IsAffineHom.of_comp W.ι (terminal.from X)
  have := affine_moduleH_subsingleton (M.restrict W.ι) q hq
  exact (affinePushforward_moduleH_subsingleton_iff W.ι (M.restrict W.ι) q).mpr
    inferInstance

variable {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hCover : iSup U = ⊤)

include hW hU hCover in
/-- The original affine cover computes zero positive cohomology for these coefficients. -/
theorem cech_subsingleton (q : ℕ) (hq : 0 < q) :
    Subsingleton (CH U (moduleAbelianSheaf (coefficients W M)) q) := by
  let : IsAffine W.toScheme := hW
  have : IsAffineHom (W.ι ≫ terminal.from X) := by
    rw [terminal.comp_from]
    infer_instance
  have : IsAffineHom W.ι := IsAffineHom.of_comp W.ι (terminal.from X)
  let : (coefficients W M).IsQuasicoherent :=
    affinePushforward_isQuasicoherent W.ι (M.restrict W.ι)
  have := coefficients_cohomology_subsingleton W hW M q hq
  exact (affineCoverCechEquiv (coefficients W M) U hU hCover q).injective.subsingleton

include hW hU hCover in
/-- Restricting any cocycle to the affine open produces an actual bounding cochain. -/
theorem exists_boundary (q : ℕ)
    (z : (C U (moduleAbelianSheaf M)).X (q + 1))
    (hz : (C U (moduleAbelianSheaf M)).d (q + 1) (q + 2) z = 0) :
    ∃ b : (C U (moduleAbelianSheaf (coefficients W M))).X q,
      (C U (moduleAbelianSheaf (coefficients W M))).d q (q + 1) b =
        ((cechComplexFunctor U).map (restriction W M).mapPresheaf).f (q + 1) z := by
  let K := C U (moduleAbelianSheaf (coefficients W M))
  let a := (cechComplexFunctor U).map (restriction W M).mapPresheaf
  have := cech_subsingleton W hW M U hU hCover (q + 1) (by omega)
  have he : K.ExactAt (q + 1) :=
    (K.exactAt_iff_isZero_homology (q + 1)).mpr
      (AddCommGrpCat.isZero_iff_subsingleton.mpr inferInstance)
  rw [K.exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff_function_exact] at he
  apply (he (a.f (q + 1) z)).mp
  change (a.f (q + 1) ≫ K.d (q + 1) (q + 2)) z = 0
  erw [a.comm]
  change a.f (q + 2) ((C U (moduleAbelianSheaf M)).d (q + 1) (q + 2) z) = 0
  rw [hz, map_zero]

end FLT.Mazur.FCurve.AffineOpenCechBoundary
