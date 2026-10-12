/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicUniversalSourceSubgroup
public import FLT.Mazur.UniversalWeierstrassCyclicModuliBridge

/-!
# The normalized full slice retains the original cubic modular object

The actual point of the full normalized slice comes from the original cubic's
etale auxiliary cover. Its image in the intended modular presheaf equals the
pullback of any original ample cyclic subgroup retained by the cubic comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
  (hφ : UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))
  (h : Nat.Coprime 4 n)
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)
local notation "f" => Over.Hom.left (pointedCubicUniversalCyclicParameter W h₂ φ hφ h)

/-- The full normalized slice point on the actual original cubic auxiliary cover. -/
def pointedCubicNormalizedPoint : (pointedCubicAuxiliaryCover W h₂).left ⟶
    cyclicNormalizedSlice n :=
  (pointedCubicUniversalCyclicParameter W h₂ φ hφ h).left ≫ cyclicNormalizationSliceMap n

variable {E : GeneralizedEllipticCurve S} (H : E.FiniteSubgroup n)
  (a : CompatibleIso ((pointedCubicFamily W).relativeCyclicSubgroup φ hφ) H)
  (hc : H.IsCyclic) (ha : H.IsAmple)

include a in
/-- The reconstructed full source retains the original ample cyclic modular class. -/
theorem pointedCubicUniversalSource_originalClass :
    cyclicSourceModuliClass n f =
      ampleCyclicClassesPullback k n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) :=
  Quotient.sound ⟨pointedCubicUniversalSourceOriginalIso W h₂ φ hφ h H a⟩

include a in
/-- The actual normalized full slice point maps to the original pulled-back modular object. -/
theorem pointedCubicNormalizedPoint_originalClass :
    (cyclicNormalizedSliceModuliMap n).app
      (Opposite.op (pointedCubicAuxiliaryCover W h₂).left)
      (ULift.up (pointedCubicNormalizedPoint W h₂ φ hφ h)) =
        ampleCyclicClassesPullback k n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  rw [pointedCubicNormalizedPoint, cyclicNormalizedSliceModuliMap_normalization]
  exact pointedCubicUniversalSource_originalClass W h₂ φ hφ h H a hc ha

end FLT.Mazur.GeneralizedEllipticCurve
