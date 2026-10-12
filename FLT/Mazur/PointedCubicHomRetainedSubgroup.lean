/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicHomSourceGroup
public import FLT.Mazur.CyclicMarkingDivisorTransport
public import FLT.Mazur.RetainedSubgroupCartierMarking

/-!
# The unrestricted source retains the original Cartier subgroup

The full DR comparison transports the original carrier and Cartier generator.
Its ideal equals the universal orbit product, even for non-etale subgroups.
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
local notation "k" => Over.hom (pointedCubicAuxiliaryCover W h₂)
local notation "f" => Over.Hom.left (pointedCubicHomAuxiliaryParameter W h₂ φ)

/-- The original pointed cubic is smooth over its actual base. -/
local instance : Smooth (pointedCubicFamily W).curve.hom := by
  let _ := integralCurveStructure_smooth W (WeierstrassCurve.IsElliptic.isUnit (W := W))
  exact inferInstanceAs (Smooth (pullback.snd (integralCurveStructure W) S.toSpecΓ))

/-- Smoothness persists on the actual auxiliary cover. -/
local instance : Smooth ((pointedCubicFamily W).baseChange k).curve.hom :=
  inferInstanceAs (Smooth (pullback.snd (pointedCubicFamily W).curve.hom k))

/-- The full reconstructed DR family is the original cubic family on its auxiliary cover. -/
def pointedCubicHomSourceCurveIso :
    (pointedCubicFamily W).baseChange k ≅ cyclicHomSourceCurve n f := by
  let d : ((pointedCubicFamily W).baseChange k).group ≅ (cyclicHomSourceCurve n f).group :=
    (CommGrp.forget _).mapIso (pointedCubicHomSourceGroupIso W h₂ φ)
  let _ : IsMonHom d.hom :=
    inferInstanceAs (IsMonHom (pointedCubicHomSourceGroupIso W h₂ φ).hom.hom.hom.hom)
  let _ := SmoothOfRelativeDimension.smooth 1 (cyclicHomSourceCurve n f).curve.hom
  exact isoOfSmoothGroup _ _ d

/-- The full DR comparison preserves every original cyclic section. -/
theorem pointedCubicHomSourceCurveIso_cyclic (b : Multiplicative (ZMod n)) :
    pullCyclicMarking k φ b ≫ (pointedCubicHomSourceCurveIso W h₂ φ).hom.group =
      cyclicHomSourceMarking n f b :=
  pointedCubicHomSourceGroupIso_cyclic W h₂ φ b

variable (H : (pointedCubicFamily W).FiniteSubgroup n)

/-- Retain the original subgroup carrier on the actual auxiliary cover. -/
def pointedCubicHomRetainedSubgroup : (cyclicHomSourceCurve n f).FiniteSubgroup n :=
  (H.baseChange k).transport (pointedCubicHomSourceCurveIso W h₂ φ)

/-- The source subgroup is compatibly isomorphic to the original pulled subgroup. -/
def pointedCubicHomRetainedIso : FiniteSubgroup.CompatibleIso (H.baseChange k)
    (pointedCubicHomRetainedSubgroup W h₂ φ H) :=
  (H.baseChange k).transportCompatibleIso (pointedCubicHomSourceCurveIso W h₂ φ)

variable {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (hφ : H.generatorCurveMarking hP = φ)

include hP in
/-- The unchanged pulled generator is Cartier on the actual retained source subgroup. -/
theorem pointedCubicHomRetained_generator :
    (pointedCubicHomRetainedSubgroup W h₂ φ H).IsCartierGenerator (H.pullGenerator k P) :=
  (H.baseChange k).transport_cartierGenerator
    (pointedCubicHomSourceCurveIso W h₂ φ) (hP.baseChange H k)

include hφ in
/-- The retained source subgroup has precisely the universal cyclic marking. -/
theorem pointedCubicHomRetained_marking :
    (pointedCubicHomRetainedSubgroup W h₂ φ H).generatorCurveMarking
      (pointedCubicHomRetained_generator W h₂ φ H hP) = cyclicHomSourceMarking n f := by
  apply MonoidHom.ext
  intro i
  have ht := (H.baseChange k).generatorCurveMarking_transport
    (pointedCubicHomSourceCurveIso W h₂ φ) (hP.baseChange H k) i
  have hb := H.generatorCurveMarking_baseChange hP k i
  rw [hφ] at hb
  exact ht.trans ((congrArg (· ≫ (pointedCubicHomSourceCurveIso W h₂ φ).hom.group) hb).trans
    (pointedCubicHomSourceCurveIso_cyclic W h₂ φ i))

include hφ in
/-- The universal product ideal is the original subgroup ideal, with all multiplicities. -/
theorem pointedCubicHomRetained_ideal :
    (pointedCubicHomRetainedSubgroup W h₂ φ H).ideal = cyclicHomSourceIdeal n f := by
  rw [← FiniteSubgroup.generatorCurveMarking_ideal _ _
    (pointedCubicHomRetained_generator W h₂ φ H hP)]
  rw [pointedCubicHomRetained_marking W h₂ φ H hP hφ]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve
