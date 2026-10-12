/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicIndependentSourceGroup
public import FLT.Mazur.UniversalWeierstrassCyclicSourceModuli

/-!
# The independent source reconstructs the original cubic cyclic subgroup

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
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)
local notation "f" => Over.Hom.left (pointedCubicIndependentParameter W h₂ φ hφ)

/-- The original pointed cubic is smooth over its actual base. -/
local instance : Smooth (pointedCubicFamily W).curve.hom := by
  let _ := integralCurveStructure_smooth W (WeierstrassCurve.IsElliptic.isUnit (W := W))
  exact inferInstanceAs (Smooth (pullback.snd (integralCurveStructure W) S.toSpecΓ))

/-- Smoothness persists on the actual auxiliary cover. -/
local instance : Smooth ((pointedCubicFamily W).baseChange k).curve.hom :=
  inferInstanceAs (Smooth (pullback.snd (pointedCubicFamily W).curve.hom k))

/-- The full reconstructed DR family is the original cubic family on its auxiliary cover. -/
def pointedCubicIndependentSourceCurveIso :
    (pointedCubicFamily W).baseChange k ≅ independentCyclicSourceCurve n f := by
  let d : ((pointedCubicFamily W).baseChange k).group ≅ (independentCyclicSourceCurve n f).group :=
    (CommGrp.forget _).mapIso (pointedCubicIndependentSourceGroupIso W h₂ φ hφ)
  let _ : IsMonHom d.hom :=
    inferInstanceAs (IsMonHom (pointedCubicIndependentSourceGroupIso W h₂ φ hφ).hom.hom.hom.hom)
  exact isoOfSmoothGroup _ _ d

/-- The full DR comparison preserves every original cyclic section. -/
theorem pointedCubicIndependentSourceCurveIso_cyclic (b : Multiplicative (ZMod n)) :
    pullCyclicMarking k φ b ≫ (pointedCubicIndependentSourceCurveIso W h₂ φ hφ).hom.group =
      independentCyclicSourceMarking n f b :=
  pointedCubicIndependentSourceGroupIso_cyclic W h₂ φ hφ b

/-- The source's actual subgroup is the original cubic cyclic subgroup after base change. -/
def pointedCubicIndependentSourceSubgroupIso :
    FiniteSubgroup.CompatibleIso (independentCyclicSourceSubgroup n f)
      (((pointedCubicFamily W).relativeCyclicSubgroup φ hφ).baseChange k) :=
  (relativeCyclicSubgroupCompatibleIso
    (E := (pointedCubicFamily W).baseChange k) (F := independentCyclicSourceCurve n f)
    (pullCyclicMarking k φ) (independentCyclicSourceMarking n f)
    (pullCyclicMarking_distinct k φ hφ) (independentCyclicSourceMarking_distinct n f)
    (pointedCubicIndependentSourceCurveIso W h₂ φ hφ)
    (pointedCubicIndependentSourceCurveIso_cyclic W h₂ φ hφ)).symm.trans
      (pullCyclicMarkingCompatibleIso k φ hφ)

/-- Any retained original subgroup comparison survives full universal source reconstruction. -/
def pointedCubicIndependentSourceOriginalIso
    {E : GeneralizedEllipticCurve S} (H : E.FiniteSubgroup n)
    (a : FiniteSubgroup.CompatibleIso ((pointedCubicFamily W).relativeCyclicSubgroup φ hφ) H) :
    FiniteSubgroup.CompatibleIso (independentCyclicSourceSubgroup n f) (H.baseChange k) :=
  (pointedCubicIndependentSourceSubgroupIso W h₂ φ hφ).trans (a.baseChange k)

/-- Reconstruction retains the original modular class, without coprimality with four. -/
theorem pointedCubicIndependentSource_originalClass
    {E : GeneralizedEllipticCurve S} (H : E.FiniteSubgroup n)
    (a : FiniteSubgroup.CompatibleIso ((pointedCubicFamily W).relativeCyclicSubgroup φ hφ) H)
    (hc : H.IsCyclic) (ha : H.IsAmple) :
    independentCyclicSourceModuliClass n f =
      FiniteSubgroup.ampleCyclicClassesPullback k n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) :=
  Quotient.sound ⟨pointedCubicIndependentSourceOriginalIso W h₂ φ hφ H a⟩

end FLT.Mazur.GeneralizedEllipticCurve
