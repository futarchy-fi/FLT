/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicUniversalSourceMarking
public import FLT.Mazur.UniversalWeierstrassCyclicSourceModuli

/-!
# The universal full source reconstructs the original cubic cyclic subgroup

The proved group comparison extends to a full DR isomorphism. Compatibility
of every cyclic section identifies the actual reconstructed source subgroup
with the pullback of the original pointed cubic subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤))) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (pointedCubicFamily W).group))
  (hφ : UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))
  (h : Nat.Coprime 4 n)
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)
local notation "f" => Over.Hom.left (pointedCubicUniversalCyclicParameter W h₂ φ hφ h)

/-- The original pointed cubic is smooth over its actual base. -/
local instance : Smooth (pointedCubicFamily W).curve.hom := by
  let _ := integralCurveStructure_smooth W (WeierstrassCurve.IsElliptic.isUnit (W := W))
  exact inferInstanceAs (Smooth (pullback.snd (integralCurveStructure W) S.toSpecΓ))

/-- Smoothness persists on the actual auxiliary cover. -/
local instance : Smooth ((pointedCubicFamily W).baseChange k).curve.hom :=
  inferInstanceAs (Smooth (pullback.snd (pointedCubicFamily W).curve.hom k))

/-- The full reconstructed DR family is the original cubic family on its auxiliary cover. -/
def pointedCubicUniversalSourceCurveIso :
    (pointedCubicFamily W).baseChange k ≅ cyclicSourceCurve n f := by
  let d : ((pointedCubicFamily W).baseChange k).group ≅ (cyclicSourceCurve n f).group :=
    (CommGrp.forget _).mapIso (pointedCubicUniversalSourceGroupIso W h₂ φ hφ h)
  let _ : IsMonHom d.hom :=
    inferInstanceAs (IsMonHom (pointedCubicUniversalSourceGroupIso W h₂ φ hφ h).hom.hom.hom.hom)
  exact isoOfSmoothGroup _ _ d

/-- The full DR comparison preserves every original cyclic section. -/
theorem pointedCubicUniversalSourceCurveIso_cyclic (b : Multiplicative (ZMod n)) :
    pullCyclicMarking k φ b ≫ (pointedCubicUniversalSourceCurveIso W h₂ φ hφ h).hom.group =
      cyclicSourceMarking n f b :=
  pointedCubicUniversalSourceGroupIso_cyclic W h₂ φ hφ h b

/-- The source's actual subgroup is the original cubic cyclic subgroup after base change. -/
def pointedCubicUniversalSourceSubgroupIso :
    FiniteSubgroup.CompatibleIso (cyclicSourceSubgroup n f)
      (((pointedCubicFamily W).relativeCyclicSubgroup φ hφ).baseChange k) :=
  (relativeCyclicSubgroupCompatibleIso (pullCyclicMarking k φ) (cyclicSourceMarking n f)
    (pullCyclicMarking_distinct k φ hφ) (cyclicSourceMarking_distinct n f)
    (pointedCubicUniversalSourceCurveIso W h₂ φ hφ h)
    (pointedCubicUniversalSourceCurveIso_cyclic W h₂ φ hφ h)).symm.trans
      (pullCyclicMarkingCompatibleIso k φ hφ)

/-- Any retained original subgroup comparison survives full universal source reconstruction. -/
def pointedCubicUniversalSourceOriginalIso
    {E : GeneralizedEllipticCurve S} (H : E.FiniteSubgroup n)
    (a : FiniteSubgroup.CompatibleIso ((pointedCubicFamily W).relativeCyclicSubgroup φ hφ) H) :
    FiniteSubgroup.CompatibleIso (cyclicSourceSubgroup n f) (H.baseChange k) :=
  (pointedCubicUniversalSourceSubgroupIso W h₂ φ hφ h).trans (a.baseChange k)

end FLT.Mazur.GeneralizedEllipticCurve
