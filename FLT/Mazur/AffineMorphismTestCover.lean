/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectedAffineSpectrum

/-!
# Affine tests lying over affine opens of the target

Pull back the cover by all affine target opens and refine each member by its
affine cover. The resulting genuine open cover retains the original morphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.AffineMorphismTestCover
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {T X : Scheme.{u}} (p : T ⟶ X)

/-- Affine source tests subordinate to the inverse images of affine target opens. -/
def cover : T.OpenCover :=
  (X.directedAffineCover.pullback₁ p).bind fun U ↦
    ((X.directedAffineCover.pullback₁ p).X U).affineCover

/-- The affine target open assigned to a source test. -/
def targetOpen (i : (cover p).I₀) : X.affineOpens := i.1

instance source_isAffine (i : (cover p).I₀) : IsAffine ((cover p).X i) :=
  inferInstanceAs (IsAffine (((X.directedAffineCover.pullback₁ p).X i.1).affineCover.X i.2))

/-- The source test maps to its assigned target open by the actual pullback projection. -/
def toOpen (i : (cover p).I₀) : (cover p).X i ⟶ (targetOpen p i).1.toScheme :=
  ((X.directedAffineCover.pullback₁ p).X i.1).affineCover.f i.2 ≫
    X.directedAffineCover.pullbackHom p i.1

/-- The local target map retains the original source-to-target morphism. -/
theorem toOpen_base (i : (cover p).I₀) :
    toOpen p i ≫ (targetOpen p i).1.ι = (cover p).f i ≫ p := by
  change (_ ≫ pullback.snd p i.1.1.ι) ≫ i.1.1.ι =
    (_ ≫ pullback.fst p i.1.1.ι) ≫ p
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]

/-- Spectrum coordinates for the target of an actual affine source test. -/
def toSpectrum (i : (cover p).I₀) : (cover p).X i ⟶
    Spec (DirectedAffineSpectrum.Ring X (targetOpen p i)) :=
  toOpen p i ≫ (targetOpen p i).1.toScheme.isoSpec.hom

/-- Returning from spectrum coordinates preserves the actual original morphism. -/
theorem toSpectrum_base (i : (cover p).I₀) :
    (toSpectrum p i ≫ (targetOpen p i).1.toScheme.isoSpec.inv) ≫
        (targetOpen p i).1.ι = (cover p).f i ≫ p := by
  simp only [toSpectrum, Category.assoc, Iso.hom_inv_id_assoc]
  exact toOpen_base p i

/-- Every point of the original test is reached by one of these affine tests. -/
theorem exists_test (x : T) : ∃ i y, (cover p).f i y = x := (cover p).exists_eq x

end FLT.Mazur.AffineMorphismTestCover
