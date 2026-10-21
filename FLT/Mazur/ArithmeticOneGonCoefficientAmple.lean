/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonAmpleBaseChange
public import FLT.Mazur.ArithmeticOneGonCoefficientIso
public import FLT.Mazur.CyclicBoundaryAmpleCurveModuli

/-!
# Actual coefficient recovery for arithmetic ample charts

The independently constructed arithmetic cubic over a coefficient extension
has the pullback ample parameter scheme. This retains its actual full universal
curve and finite subgroup and works over arbitrary coefficient rings.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open CyclicBoundaryParameter GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (t : R) (ht : IsUnit (1 + 432 * t)) (n : ℕ) [NeZero n]
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "E" => curve t ht
local notation "F" => curve (algebraMap R S t) (coefficientParameter_isUnit t ht)

local instance coefficientAmpleGroup_separated : IsSeparated ((E).baseChange (g)).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (E).group.hom (g)))

local instance coefficientAmpleGroup_smooth :
    SmoothOfRelativeDimension 1 ((E).baseChange (g)).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) (E).group.hom (g)
    inferInstance

/-- The independently constructed coefficient chart projects to the original ample chart. -/
def coefficientAmpleToOriginal : ampleParameter (F) n ⟶ ampleParameter (E) n :=
  ampleCurveTransport (coefficientIso t ht) n ≫ ampleBaseChangeToOriginal (g) (E) n

/-- The independently constructed coefficient ample chart is the actual pullback scheme. -/
def coefficientAmpleParameterIso :
    ampleParameter (F) n ≅ pullback (ampleParameterBase (E) n) (g) :=
  ampleCurveTransportIso (coefficientIso t ht) n ≪≫ (ampleBaseChangeIso (g) (E) n).symm

/-- The coefficient comparison retains the actual original ample parameter projection. -/
@[reassoc] theorem coefficientAmpleParameterIso_original :
    (coefficientAmpleParameterIso (S := S) t ht n).hom ≫
      pullback.fst (ampleParameterBase (E) n) (g) = coefficientAmpleToOriginal t ht n := by
  change (ampleCurveTransport (coefficientIso t ht) n ≫
    (ampleBaseChangeIso (g) (E) n).inv) ≫ _ = _
  rw [Category.assoc]
  exact congrArg (ampleCurveTransport (coefficientIso t ht) n ≫ ·)
    (ampleBaseChangeToOriginal_isPullback (g) (E) n).isoPullback_hom_fst

/-- The coefficient chart comparison retains the independently constructed structure map. -/
@[reassoc] theorem coefficientAmpleParameterIso_base :
    (coefficientAmpleParameterIso (S := S) t ht n).hom ≫
      pullback.snd (ampleParameterBase (E) n) (g) = ampleParameterBase (F) n := by
  change (ampleCurveTransport (coefficientIso t ht) n ≫
    (ampleBaseChangeIso (g) (E) n).inv) ≫ _ = _
  rw [Category.assoc]
  exact (congrArg (ampleCurveTransport (coefficientIso t ht) n ≫ ·)
    (ampleBaseChangeToOriginal_isPullback (g) (E) n).isoPullback_hom_snd).trans
      (ampleCurveTransport_base (coefficientIso t ht) n)

/-- Coefficient recovery gives a cartesian square of independently constructed ample charts. -/
theorem coefficientAmpleToOriginal_isPullback :
    IsPullback (coefficientAmpleToOriginal (S := S) t ht n) (ampleParameterBase (F) n)
      (ampleParameterBase (E) n) (g) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (coefficientAmpleParameterIso t ht n)
    (coefficientAmpleParameterIso_original t ht n) (coefficientAmpleParameterIso_base t ht n)
  rw [← coefficientAmpleParameterIso_original, Category.assoc, pullback.condition,
    ← Category.assoc, coefficientAmpleParameterIso_base]

/-- Recovery retains the actual finite subgroup and full generalized curve. -/
def coefficientAmpleSubgroupIso :
    CompatibleIso (ampleUniversalLevel (F) n).val.2
      ((ampleUniversalLevel (E) n).val.2.baseChange
        (coefficientAmpleToOriginal (S := S) t ht n)) :=
  (ampleCurveTransportSubgroupIso (coefficientIso t ht) n).trans
    (((ampleBaseChangeSubgroupIso (g) (E) n).baseChange
      (ampleCurveTransport (coefficientIso t ht) n)).trans
        ((ampleUniversalLevel (E) n).val.2.compatibleBaseChangeComp
          (ampleBaseChangeToOriginal (g) (E) n)
          (ampleCurveTransport (coefficientIso t ht) n)).symm)

/-- The actual modular transformation commutes with arbitrary arithmetic coefficient extension. -/
theorem coefficientAmpleModuliMap :
    ampleModuliMap (F) n = uliftYoneda.map (coefficientAmpleToOriginal (S := S) t ht n) ≫
      ampleModuliMap (E) n := by
  rw [ampleModuliMap_curveTransport (coefficientIso t ht) n,
    ampleModuliMap_baseChange, coefficientAmpleToOriginal, Functor.map_comp, Category.assoc]

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
