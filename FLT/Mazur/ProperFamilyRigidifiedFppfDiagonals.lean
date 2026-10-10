/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedFppfPairs
public import FLT.Mazur.ProperFamilyRigidifiedNamedTransitions
public import FLT.Mazur.RelativePicardCoverDiagonal
public import FLT.Mazur.SchemeIndependentDiagonalIdentity
public import FLT.Mazur.SchemeGeometricDescentData

/-!
# Original diagonal laws for rigidified fppf pair isomorphisms

The actual pair transitions normalize to the identity along each member
diagonal. The original pair chart then gives the required total-cover law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity SchemeIndependentPairNormalization
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)

/-- The original base-pair transition satisfies its actual total-space diagonal equation. -/
theorem rigidifiedFamilyPairTransition_diagonal (i : 𝒰.I₀) :
    SchemeOverlapDiagonalChart.DiagonalCompatible
      (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i i))
      (relativeTotalMap f (relativeCoverPairRight T 𝒰 i i))
      (relativeTotalMap f (relativeCoverDiagonal T 𝒰 i))
      (relativeCoverDiagonal_total_left f T 𝒰 i)
      (relativeCoverDiagonal_total_right f T 𝒰 i)
      (rigidifiedFamilyRepresentative f e he T 𝒰 a i).1.val
      (rigidifiedFamilyPairTransition f e he T 𝒰 a ha i i).val := by
  have h := rigidifiedTransition_normalize_named f e he
    (relativeCoverDiagonal T 𝒰 i) (relativeCoverPairLeft T 𝒰 i i)
    (relativeCoverPairRight T 𝒰 i i) (𝟙 _) (𝟙 _)
    (relativeCoverDiagonal_left T 𝒰 i) (relativeCoverDiagonal_right T 𝒰 i)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a i)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a i)
    (rigidifiedFamilyRepresentative_matching f e he T 𝒰 a ha i i) rfl
  rw [rigidifiedTransition_refl] at h
  exact diagonal_of_normalize_named_refl _ _ _ _
    (relativeTotalMap_id f (relativeCoverMember T 𝒰 i)) _ _ _ _ h

/-- The originally constructed pair isomorphism satisfies the original member diagonal. -/
theorem rigidifiedFamilyPairIso_diagonal (i : 𝒰.I₀) :
    SchemeGeometricDescent.Diagonal ((relativeTotalCover f T 𝒰).f i)
      (rigidifiedFamilyRepresentative f e he T 𝒰 a i).1.val
      (rigidifiedFamilyPairIso f e he T 𝒰 a ha i i) :=
  SchemeOverlapDiagonalChart.normalize_diagonal
    (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i i))
    (relativeTotalMap f (relativeCoverPairRight T 𝒰 i i))
    (relativeCoverPairTotalIso f T 𝒰 i i).inv _ _
    (relativeCoverPairTotalIso_inv_fst f T 𝒰 i i)
    (relativeCoverPairTotalIso_inv_snd f T 𝒰 i i)
    (relativeTotalMap f (relativeCoverDiagonal T 𝒰 i))
    (Limits.pullback.diagonal ((relativeTotalCover f T 𝒰).f i))
    (relativeCoverDiagonal_total_inverse f T 𝒰 i)
    (relativeCoverDiagonal_total_left f T 𝒰 i)
    (relativeCoverDiagonal_total_right f T 𝒰 i) _ _ _ _
    (rigidifiedFamilyPairTransition_diagonal f e he T 𝒰 a ha i)

end FLT.Mazur.SchemePicard
