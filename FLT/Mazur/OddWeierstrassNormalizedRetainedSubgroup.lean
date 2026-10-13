/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedCyclicSource
public import FLT.Mazur.RetainedSubgroupCartierMarking
public import FLT.Mazur.CyclicMarkingDivisorTransport

/-!
# The actual original subgroup on its normalized odd cyclic source

Full curve transport retains the subgroup carrier, its Cartier generator and
all cyclic labels. Equality of ideals includes every multiplicity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {n : ℕ} [NeZero n]
  (p : (Over.map (auxiliaryCoefficientBase g)).obj (𝟙_ (Over (Spec (.of R)))) ⟶ levelThree)
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over (Spec (.of R))) ⟶ (auxiliaryPullbackGroup g).X))
local notation "f" => Over.Hom.left (auxiliaryNormalizedCyclicParameter g p φ)

/-- The entire original curve agrees with the reconstructed normalized source. -/
irreducible_def auxiliaryCyclicSourceCurveIso :
    auxiliaryPullbackCurve g ≅ cyclicHomSourceCurve n f :=
  (auxiliaryNormalizationCurveIso g).symm ≪≫ auxiliaryNormalizedCyclicSourceCurveIso g p φ

/-- The full comparison carries each unchanged original cyclic label. -/
theorem auxiliaryCyclicSourceCurveIso_marking (i : Multiplicative (ZMod n)) :
    φ i ≫ (auxiliaryCyclicSourceCurveIso g p φ).hom.group =
      cyclicHomSourceMarking n f i := by
  rw [auxiliaryCyclicSourceCurveIso_def]
  change φ i ≫ (auxiliaryNormalizationCurveIso g).inv.group ≫
    (auxiliaryNormalizedCyclicSourceCurveIso g p φ).hom.group = _
  rw [auxiliaryNormalizationCurveIso_inv_group, ← Category.assoc]
  exact auxiliaryNormalizedCyclicSourceCurveIso_marking g p φ i

variable (H : (auxiliaryPullbackCurve g).FiniteSubgroup n)

/-- Keep the actual original subgroup carrier on the normalized cyclic source. -/
def auxiliaryCyclicSourceRetainedSubgroup : (cyclicHomSourceCurve n f).FiniteSubgroup n :=
  H.transport (auxiliaryCyclicSourceCurveIso g p φ)

/-- The retained subgroup has a full compatible comparison with the original. -/
def auxiliaryCyclicSourceRetainedIso :
    CompatibleIso H (auxiliaryCyclicSourceRetainedSubgroup g p φ H) :=
  H.transportCompatibleIso (auxiliaryCyclicSourceCurveIso g p φ)

variable {P : 𝟙_ (Over (Spec (.of R))) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (hφ : H.generatorCurveMarking hP = φ)

include hP in
/-- The original Cartier generator survives normalization on its identical carrier. -/
theorem auxiliaryCyclicSourceRetained_generator :
    (auxiliaryCyclicSourceRetainedSubgroup g p φ H).IsCartierGenerator P :=
  H.transport_cartierGenerator (auxiliaryCyclicSourceCurveIso g p φ) hP

include hφ in
/-- The actual generator marking is exactly the reconstructed unrestricted marking. -/
theorem auxiliaryCyclicSourceRetained_marking :
    (auxiliaryCyclicSourceRetainedSubgroup g p φ H).generatorCurveMarking
      (auxiliaryCyclicSourceRetained_generator g p φ H hP) = cyclicHomSourceMarking n f := by
  apply MonoidHom.ext
  intro i
  have ht := H.generatorCurveMarking_transport (auxiliaryCyclicSourceCurveIso g p φ) hP i
  rw [hφ] at ht
  exact ht.trans (auxiliaryCyclicSourceCurveIso_marking g p φ i)

include hφ in
/-- The normalized parameter retains the full original subgroup ideal with all factors. -/
theorem auxiliaryCyclicSourceRetained_ideal :
    (auxiliaryCyclicSourceRetainedSubgroup g p φ H).ideal = cyclicHomSourceIdeal n f := by
  rw [← generatorCurveMarking_ideal (cyclicHomSourceCurve n f)
    (auxiliaryCyclicSourceRetainedSubgroup g p φ H)
    (auxiliaryCyclicSourceRetained_generator g p φ H hP)]
  rw [auxiliaryCyclicSourceRetained_marking g p φ H hP hφ]
  rfl

end FLT.Mazur.OddWeierstrassParameter
