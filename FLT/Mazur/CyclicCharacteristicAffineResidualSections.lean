/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualArrows
public import FLT.Mazur.SchemeRelationInvariantAffineUniversal

/-!
# Full residual section rings on the actual affine refinement

The original invariant sheaf pulls back into the equalizer of the full restricted
arrow maps. The spectrum of that equalizer is universal for invariant affine tests.
The comparison is constructed without assuming surjectivity of the sheaf pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- The full residual invariant ring on an actual affine parameter chart. -/
def affineResidualSections : Subring Γ(invariantAffineChart n i, ⊤) :=
  SchemeEffectiveEpiSections.compatibleFunctions
    (affineResidualSource n i) (affineResidualTarget n i)

/-- The original quotient sheaf pullback to the selected affine parameter scheme. -/
def affineInvariantSectionMap :
    (invariantSheaf n).obj.obj (op (affineOrbitOpen n i)) ⟶
      Γ(invariantAffineChart n i, ⊤) :=
  (invariantOpenSectionsIso n _).inv ≫
    LocallyRingedSpace.Γ.map (affineToInvariantOpen n i).op

/-- The actual pullback preserves every full residual arrow, including infinitesimal ones. -/
theorem affineInvariantSectionMap_condition :
    affineInvariantSectionMap n i ≫ (affineResidualSource n i).appTop =
      affineInvariantSectionMap n i ≫ (affineResidualTarget n i).appTop := by
  have h := congrArg (fun f => LocallyRingedSpace.Γ.map f.op)
    (affineToInvariantOpen_condition n i)
  change LocallyRingedSpace.Γ.map ((affineToInvariantOpen n i).op ≫
    (affineResidualSource n i).toLRSHom.op) =
      LocallyRingedSpace.Γ.map ((affineToInvariantOpen n i).op ≫
        (affineResidualTarget n i).toLRSHom.op) at h
  simp only [Functor.map_comp] at h
  exact congrArg ((invariantOpenSectionsIso n _).inv ≫ ·) h

/-- The genuine section comparison into the full residual invariant ring. -/
def affineResidualSectionMap :
    (invariantSheaf n).obj.obj (op (affineOrbitOpen n i)) →+* affineResidualSections n i :=
  (affineInvariantSectionMap n i).hom.codRestrict _ (fun s => by
    change (affineResidualSource n i).appTop (affineInvariantSectionMap n i s) =
      (affineResidualTarget n i).appTop (affineInvariantSectionMap n i s)
    exact congrArg (fun f => f s) (affineInvariantSectionMap_condition n i))

/-- The section comparison retains the exact original pullback of regular functions. -/
theorem affineResidualSectionMap_val
    (s : (invariantSheaf n).obj.obj (op (affineOrbitOpen n i))) :
    (affineResidualSectionMap n i s).val = affineInvariantSectionMap n i s := rfl

/-- The affine spectrum of the full residual invariant ring on the original affine chart. -/
def affineResidualSpectrum : Scheme :=
  SchemeRelationInvariantSpectrum.target (affineResidualSource n i) (affineResidualTarget n i)

/-- The original affine chart maps to its full residual invariant spectrum. -/
def affineResidualProjection : invariantAffineChart n i ⟶ affineResidualSpectrum n i :=
  SchemeRelationInvariantSpectrum.projection
    (affineResidualSource n i) (affineResidualTarget n i)

/-- All maps into affine schemes respecting the full restricted relation factor uniquely. -/
theorem affineResidualProjection_existsUnique {Y : Scheme} [IsAffine Y]
    (g : invariantAffineChart n i ⟶ Y)
    (hg : affineResidualSource n i ≫ g = affineResidualTarget n i ≫ g) :
    ∃! h : affineResidualSpectrum n i ⟶ Y, affineResidualProjection n i ≫ h = g :=
  SchemeRelationInvariantSpectrum.existsUnique_affine_factor _ _ g hg

end FLT.Mazur.CyclicCharacteristicOrbit
