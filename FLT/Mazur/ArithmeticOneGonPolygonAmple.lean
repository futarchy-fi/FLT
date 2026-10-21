/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonBoundaryFiber
public import FLT.Mazur.ArithmeticOneGonAmpleBaseChange
public import FLT.Mazur.PolygonBoundaryAmpleParameter
public import FLT.Mazur.CyclicBoundaryAmpleCurveModuli

/-!
# The original pinched polygon chart in an arithmetic boundary fiber

At every field-valued zero of the arithmetic parameter, the actual pinched
one-gon's ample chart is the pullback arithmetic ample chart. The construction
uses the full original pinching isomorphism and retains the universal subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonBoundaryFiber
open CyclicBoundaryParameter ArithmeticOneGonGeneralizedCurve
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (K : Type) [Field K] [Algebra R K]
  (t : R) (ht : IsUnit (1 + 432 * t)) (hzero : algebraMap R K t = 0)
  (n : ℕ) [NeZero n]
local notation "N" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "E" => curve t ht

local instance originalPolygonAmpleGroup_separated : IsSeparated (N).group.hom :=
  PolygonCyclicBoundary.splitBoundaryGroup_separated K 1

local instance originalPolygonAmpleGroup_smooth :
    SmoothOfRelativeDimension 1 (N).group.hom :=
  PolygonCyclicBoundary.splitBoundaryGroup_relativeDimension K 1

local instance polygonArithmeticAmpleGroup_separated :
    IsSeparated ((E).baseChange (g)).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (E).group.hom (g)))

local instance polygonArithmeticAmpleGroup_smooth :
    SmoothOfRelativeDimension 1 ((E).baseChange (g)).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) (E).group.hom (g)
    inferInstance

/-- The original pinched one-gon chart maps to the arithmetic ample chart. -/
def polygonAmpleToArithmetic : ampleParameter (N) n ⟶ ampleParameter (E) n :=
  ampleCurveTransport (curveIso K t ht hzero) n ≫ ampleBaseChangeToOriginal (g) (E) n

/-- The pinched polygon parameter scheme is the actual arithmetic chart fiber. -/
def polygonArithmeticAmpleIso :
    ampleParameter (N) n ≅ pullback (ampleParameterBase (E) n) (g) :=
  ampleCurveTransportIso (curveIso K t ht hzero) n ≪≫
    (ampleBaseChangeIso (g) (E) n).symm

/-- The comparison retains the original arithmetic ample parameter projection. -/
@[reassoc] theorem polygonArithmeticAmpleIso_original :
    (polygonArithmeticAmpleIso K t ht hzero n).hom ≫
      pullback.fst (ampleParameterBase (E) n) (g) = polygonAmpleToArithmetic K t ht hzero n := by
  change (ampleCurveTransport (curveIso K t ht hzero) n ≫
    (ampleBaseChangeIso (g) (E) n).inv) ≫ _ = _
  rw [Category.assoc]
  exact congrArg (ampleCurveTransport (curveIso K t ht hzero) n ≫ ·)
    (ampleBaseChangeToOriginal_isPullback (g) (E) n).isoPullback_hom_fst

/-- The original full polygon and its finite subgroup retain their arithmetic presentation. -/
def polygonArithmeticAmpleSubgroupIso :
    CompatibleIso (ampleUniversalLevel (N) n).val.2
      ((ampleUniversalLevel (E) n).val.2.baseChange (polygonAmpleToArithmetic K t ht hzero n)) :=
  (ampleCurveTransportSubgroupIso (curveIso K t ht hzero) n).trans
    (((ampleBaseChangeSubgroupIso (g) (E) n).baseChange
      (ampleCurveTransport (curveIso K t ht hzero) n)).trans
        ((ampleUniversalLevel (E) n).val.2.compatibleBaseChangeComp
          (ampleBaseChangeToOriginal (g) (E) n)
          (ampleCurveTransport (curveIso K t ht hzero) n)).symm)

/-- The polygon and arithmetic chart transformations agree on every scheme-valued test. -/
theorem polygonArithmeticAmpleModuliMap :
    ampleModuliMap (N) n = uliftYoneda.map (polygonAmpleToArithmetic K t ht hzero n) ≫
      ampleModuliMap (E) n := by
  rw [ampleModuliMap_curveTransport (curveIso K t ht hzero) n,
    ampleModuliMap_baseChange, polygonAmpleToArithmetic, Functor.map_comp, Category.assoc]

end FLT.Mazur.ArithmeticOneGonBoundaryFiber
