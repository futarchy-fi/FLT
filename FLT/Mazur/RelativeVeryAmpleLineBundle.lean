/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineBundleTensorPullback
public import FLT.Mazur.ProjectiveSpaceProper
public import FLT.Mazur.ProjectiveTwistAffineBaseChange
public import FLT.Mazur.ProjectiveTwistingSheafTensor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Relative very ample line bundles

Presentations use actual module sheaves and closed immersions into polynomial
projective space. A proper morphism with a projective immersion supplies such
presentations over every affine target open. The tensor-power comparisons
include the structure module in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

variable {X Y : Scheme.{u}}

/-- An isomorphism of sheaves induces isomorphisms of all natural tensor powers. -/
def tensorPowerCongr {M N : X.Modules} (e : M ≅ N) :
    ∀ n : ℕ, tensorPower M n ≅ tensorPower N n
  | 0 => Iso.refl _
  | n + 1 => ModuleSheafTensor.congr e (tensorPowerCongr e n)

/-- Restriction commutes with the actual tensor powers. -/
def tensorPowerRestrictIso (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j] :
    ∀ n : ℕ, (tensorPower M n).restrict j ≅ tensorPower (M.restrict j) n
  | 0 => Scheme.Modules.restrictUnitIso j
  | n + 1 => ModuleSheafTensor.restrictIso M (tensorPower M n) j ≪≫
      ModuleSheafTensor.congr (Iso.refl _) (tensorPowerRestrictIso M j n)

/-- The restriction comparison in degree zero is the structure-module comparison. -/
@[simp]
lemma tensorPowerRestrictIso_zero (M : Y.Modules) (j : X ⟶ Y) [IsOpenImmersion j] :
    tensorPowerRestrictIso M j 0 = Scheme.Modules.restrictUnitIso j := rfl

end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

namespace FLT.Mazur.ProjectiveSpace

/-- Powers of the actual hyperplane bundle are the integer twisting sheaves. -/
def OOneTensorPowerIso (A : Type) [CommRing A] (d : ℕ) :
    ∀ n : ℕ, tensorPower (O A d 1) n ≅ O A d (n : ℤ)
  | 0 => (OZeroIso A d).symm
  | n + 1 => ModuleSheafTensor.congr (Iso.refl _) (OOneTensorPowerIso A d n) ≪≫
      OTensorIso A d 1 n ≪≫ eqToIso (by congr 1; omega)

/-- Tensor powers of a pulled-back hyperplane bundle identify with pulled-back twists. -/
def pullbackOOnePowerIso {A : Type} [CommRing A] {X : Scheme} {d : ℕ}
    (i : X ⟶ space A (Fin (d + 1))) (n : ℕ) :
    tensorPower ((Scheme.Modules.pullback i).obj (O A d 1)) n ≅
      (Scheme.Modules.pullback i).obj (O A d (n : ℤ)) :=
  (tensorPowerIso i (O A d 1) n).symm ≪≫
    (Scheme.Modules.pullback i).mapIso (OOneTensorPowerIso A d n)

/-- The power-zero identification uses the canonical pullback of the structure module. -/
@[simp]
lemma pullbackOOnePowerIso_zero {A : Type} [CommRing A] {X : Scheme} {d : ℕ}
    (i : X ⟶ space A (Fin (d + 1))) :
    pullbackOOnePowerIso i 0 = (modulePullbackUnitIso i).symm ≪≫
      (Scheme.Modules.pullback i).mapIso (OZeroIso A d).symm := rfl

/-- A closed projective presentation of a module sheaf over an affine base. -/
structure VeryAmplePresentation {A : Type} [CommRing A] {X : Scheme}
    (f : X ⟶ Spec (.of A)) (L : X.Modules) where
  /-- Dimension of the polynomial projective target. -/
  dimension : ℕ
  /-- The morphism presenting the source as a closed projective subscheme. -/
  embedding : X ⟶ space A (Fin (dimension + 1))
  /-- The presentation morphism is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion embedding
  /-- The embedding commutes with the specified structural map. -/
  over : embedding ≫ baseProjection A _ = f
  /-- The presented sheaf is the actual pullback of the hyperplane bundle. -/
  coefficientIso : L ≅ (Scheme.Modules.pullback embedding).obj (O A dimension 1)

attribute [instance] VeryAmplePresentation.isClosedImmersion

/-- Relative very ampleness, expressed on every affine target open. -/
def RelativeVeryAmple {X Y : Scheme} (f : X ⟶ Y) (L : X.Modules) : Prop :=
  ∀ (U : Y.Opens) (hU : IsAffineOpen U),
    Nonempty (VeryAmplePresentation ((f ∣_ U) ≫ hU.isoSpec.hom)
      (L.restrict (f ⁻¹ᵁ U).ι))

namespace VeryAmplePresentation

variable {A : Type} [CommRing A] {X : Scheme} {f : X ⟶ Spec (.of A)}
  {L : X.Modules} (p : VeryAmplePresentation f L)

include p in
/-- A presented sheaf is locally free of rank one. -/
theorem locallyFreeRankOne : LocallyFreeRankOne L :=
  ((O_locallyFreeRankOne A p.dimension 1).pullback p.embedding).of_iso p.coefficientIso.symm

/-- All natural powers of a presentation have the expected projective coefficients. -/
def powerIso (n : ℕ) : tensorPower L n ≅
    (Scheme.Modules.pullback p.embedding).obj (O A p.dimension (n : ℤ)) :=
  tensorPowerCongr p.coefficientIso n ≪≫ pullbackOOnePowerIso p.embedding n

/-- A presentation remains a presentation after changing its sheaf by an isomorphism. -/
def ofIso {M : X.Modules} (e : M ≅ L) : VeryAmplePresentation f M where
  dimension := p.dimension
  embedding := p.embedding
  isClosedImmersion := p.isClosedImmersion
  over := p.over
  coefficientIso := e ≪≫ p.coefficientIso

end VeryAmplePresentation

variable {A : Type} [CommRing A] {X Y : Scheme} {d : ℕ}
  (f : X ⟶ Y) (q : Y ⟶ Spec (.of A)) (i : X ⟶ space A (Fin (d + 1)))
  (h : i ≫ baseProjection A _ = f ≫ q)

/-- On an affine target open, properness upgrades the coefficient immersion to a closed one. -/
theorem targetOpenCoefficientMap_isClosedImmersion [IsProper f] [IsImmersion i]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsClosedImmersion (targetOpenCoefficientMap f q i h U) := by
  let j := targetOpenCoefficientMap f q i h U
  have : IsImmersion (j ≫ coefficientMap (openCoefficientRingMap q U) _) := by
    dsimp only [j]
    rw [targetOpenCoefficientMap_comp]
    infer_instance
  have : IsImmersion j := IsImmersion.of_comp j (coefficientMap (openCoefficientRingMap q U) _)
  have : IsProper (j ≫ baseProjection Γ(Y, U) _) := by
    dsimp only [j]
    rw [targetAffineOpenCoefficientMap_baseProjection f q i h hU]
    infer_instance
  have : IsProper j := IsProper.of_comp j (baseProjection Γ(Y, U) _)
  exact IsClosedImmersion.of_isPreimmersion j j.isClosedMap.isClosed_range

/-- The affine-open presentation constructed from properness and a projective immersion. -/
def targetAffinePresentation [IsProper f] [IsImmersion i]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    VeryAmplePresentation ((f ∣_ U) ≫ hU.isoSpec.hom)
      (((Scheme.Modules.pullback i).obj (O A d 1)).restrict (f ⁻¹ᵁ U).ι) where
  dimension := d
  embedding := targetOpenCoefficientMap f q i h U
  isClosedImmersion := targetOpenCoefficientMap_isClosedImmersion f q i h U hU
  over := targetAffineOpenCoefficientMap_baseProjection f q i h hU
  coefficientIso := targetAffineOpenCoefficientOOneIso f q i h U

include q h in
/-- Relative very ampleness is a conclusion of the geometric presentation. -/
theorem relativeVeryAmple_pullbackOOne [IsProper f] [IsImmersion i] :
    RelativeVeryAmple f ((Scheme.Modules.pullback i).obj (O A d 1)) :=
  fun U hU ↦ ⟨targetAffinePresentation f q i h U hU⟩

/-- Restricting any power and transporting coefficients gives the actual `O(n)` pullback. -/
def targetOpenPowerIso (U : Y.Opens) (n : ℕ) :
    (tensorPower ((Scheme.Modules.pullback i).obj (O A d 1)) n).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (targetOpenCoefficientMap f q i h U)).obj
        (O Γ(Y, U) d (n : ℤ)) :=
  (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackOOnePowerIso i n) ≪≫
    targetOpenCoefficientTwistingIso f q i h U (n : ℤ)

/-- The degree-zero coefficient transport starts with the actual structure module. -/
def targetOpenZeroIso (U : Y.Opens) :
    (structureModule X).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (targetOpenCoefficientMap f q i h U)).obj (O Γ(Y, U) d 0) :=
  targetOpenPowerIso f q i h U 0

end FLT.Mazur.ProjectiveSpace
