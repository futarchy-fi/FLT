/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCoefficientAmple
public import FLT.Mazur.ArithmeticOneGonFaithfulModuli

/-!
# The whole arithmetic faithful chart retains coefficient recovery

No faithful parameters are lost by the ample restriction. The actual coefficient
comparison preserves the full universal subgroup and commutes with the original
faithful modular transformation on every scheme-valued test.
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

local instance coefficientFaithfulGroup_separated :
    IsSeparated ((E).baseChange (g)).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (E).group.hom (g)))

local instance coefficientFaithfulGroup_smooth :
    SmoothOfRelativeDimension 1 ((E).baseChange (g)).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) (E).group.hom (g)
    inferInstance

/-- The full independent coefficient faithful chart retains its original parameter. -/
def coefficientFaithfulToOriginal :
    (cyclicFaithfulParameter (F).group n).left ⟶ (cyclicFaithfulParameter (E).group n).left :=
  (faithfulCurveTransportIso (coefficientIso t ht) n).hom.left ≫
    faithfulBaseChangeToOriginal (g) (E).group n

/-- Coefficient recovery commutes with passage from the whole faithful chart to the ample chart. -/
@[reassoc] theorem coefficientFaithfulToAmple :
    faithfulToAmple (algebraMap R S t) (coefficientParameter_isUnit t ht) n ≫
        coefficientAmpleToOriginal t ht n =
      coefficientFaithfulToOriginal (S := S) t ht n ≫ faithfulToAmple t ht n := by
  apply (cancel_mono (ampleParameterOpen (E) n).ι).mp
  simp only [coefficientAmpleToOriginal, coefficientFaithfulToOriginal, Category.assoc,
    ampleBaseChangeToOriginal_inclusion, ampleCurveTransport_inclusion_assoc,
    faithfulToAmple_inclusion_assoc, faithfulToAmple_inclusion, Category.comp_id]

/-- The actual full faithful universal subgroup is retained by coefficient recovery. -/
def coefficientFaithfulSubgroupIso :
    CompatibleIso (faithfulUniversalSubgroup (F) n)
      ((faithfulUniversalSubgroup (E) n).baseChange
        (coefficientFaithfulToOriginal (S := S) t ht n)) :=
  (faithfulTransportSubgroupIso (coefficientIso t ht) n).trans
    (((faithfulBaseChangeSubgroupIso (g) (E) n).baseChange
      (faithfulCurveTransportIso (coefficientIso t ht) n).hom.left).trans
        ((faithfulUniversalSubgroup (E) n).compatibleBaseChangeComp
          (faithfulBaseChangeToOriginal (g) (E).group n)
          (faithfulCurveTransportIso (coefficientIso t ht) n).hom.left).symm)

/-- The whole faithful modular map commutes with actual arithmetic coefficient change. -/
theorem coefficientFaithfulModuliMap :
    faithfulBoundaryModuliMap (algebraMap R S t) (coefficientParameter_isUnit t ht) n =
      uliftYoneda.map (coefficientFaithfulToOriginal (S := S) t ht n) ≫
        faithfulBoundaryModuliMap t ht n := by
  unfold faithfulBoundaryModuliMap
  rw [coefficientAmpleModuliMap t ht n, ← Category.assoc, ← Functor.map_comp,
    coefficientFaithfulToAmple, Functor.map_comp, Category.assoc]

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
