/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalIntegralActionSource
public import FLT.Mazur.WeierstrassSuccessiveXIncidenceTransport

/-!
# Integral transport of the actual horizontal action to the successive chart

The original action at scale pi^(k+1) is restricted where both original
incidences are units. Its input and output then map to the original successive
chart at scales pi^k, pi. Both original branch residues factor through this
single integral refinement; no shifted finite model is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationX WeierstrassModificationReesCoordinates WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : WeierstrassDividedDepth.Data W π (k + 1)) (hπ : π ≠ 0)
local notation "H" => horizontalReesChart W (π ^ (k + 1))
local notation "O" => SmoothHorizontalActionRing d
local notation "B" => WeierstrassModificationX.Coordinate W (π ^ k * π) d.b3 d.b4 d.b6
local notation "A" => WeierstrassSuccessiveX.Coordinate W (π ^ k) π d.b3 d.b4 d.b6
local notation "t" => WeierstrassModificationX.t W (π ^ k * π) d.b3 d.b4 d.b6

local notation "tH" => (horizontalScale W (π ^ (k + 1)) : H)
local notation "vH" => (horizontalVertical W (π ^ (k + 1)) : H)

include hπ in
/-- The original fraction functions satisfy the product-scale incidence equation. -/
theorem successiveHorizontalEquation_incidence :
    tH * (vH ^ 2 + (algebraMap R H W.a₁ + algebraMap R H d.b3 * tH) * vH -
      (algebraMap R H W.a₂ + algebraMap R H d.b4 * tH + algebraMap R H d.b6 * tH ^ 2)) =
      algebraMap R H (π ^ k * π) := by
  let E := horizontalReesChartEquiv W (π ^ (k + 1)) d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6 (pow_ne_zero (k + 1) hπ)
  have h := congrArg E (WeierstrassModificationX.incidence W (π ^ (k + 1))
    d.b3 d.b4 d.b6)
  dsimp only [E] at h
  simp only [WeierstrassModificationX.x, map_mul, map_sub, map_add, map_pow,
    AlgEquiv.commutes, horizontalEquiv_t, horizontalEquiv_v] at h
  exact h.trans ((map_pow (algebraMap R H) π (k + 1)).symm.trans
    (congrArg (algebraMap R H) (pow_succ π k)))

/-- The product-scale equation functions in the original horizontal fraction algebra. -/
def successiveHorizontalEquationMap : B →ₐ[R] H :=
  WeierstrassModificationX.evaluation W (π ^ k * π) d.b3 d.b4 d.b6
    (horizontalScale W (π ^ (k + 1))) (horizontalVertical W (π ^ (k + 1)))
    (successiveHorizontalEquation_incidence d hπ)

/-- The comparison preserves the original incidence ratio exactly. -/
theorem successiveHorizontalEquationMap_t :
    successiveHorizontalEquationMap d hπ t = horizontalScale W (π ^ (k + 1)) :=
  WeierstrassModificationX.evaluation_t ..

/-- The comparison also preserves the original slope ratio. -/
theorem successiveHorizontalEquationMap_v :
    successiveHorizontalEquationMap d hπ
      (WeierstrassModificationX.v W (π ^ k * π) d.b3 d.b4 d.b6) =
        horizontalVertical W (π ^ (k + 1)) :=
  WeierstrassModificationX.evaluation_v ..

attribute [local irreducible] SmoothHorizontalActionRing successiveHorizontalEquationMap

/-- The actual integral input in product-scale equation coordinates. -/
def successiveHorizontalOriginalInput : B →ₐ[R] O :=
  (smoothHorizontalIntegralInput d).comp (successiveHorizontalEquationMap d hπ)

/-- The actual integral action output in the same original equation coordinates. -/
def successiveHorizontalOriginalOutput : B →ₐ[R] O :=
  (smoothHorizontalIntegralOutput d).comp (successiveHorizontalEquationMap d hπ)

local notation "f" => successiveHorizontalOriginalInput d hπ
local notation "g" => successiveHorizontalOriginalOutput d hπ

/-- The single integral open where both original incidences are inverted. -/
abbrev SmoothSuccessiveActionOpen := IncidencePairOpen W (π ^ k) π d.b3 d.b4 d.b6 f g
local notation "L" => SmoothSuccessiveActionOpen d hπ

/-- The actual original input transported to the successive chart. -/
def smoothSuccessiveIntegralInput : A →ₐ[R] L :=
  incidencePairFirst W (π ^ k) π d.b3 d.b4 d.b6 f g

/-- The actual original output transported to the same successive chart. -/
def smoothSuccessiveIntegralOutput : A →ₐ[R] L :=
  incidencePairSecond W (π ^ k) π d.b3 d.b4 d.b6 f g

/-- Every original modification function agrees before residue specialization on the input. -/
theorem smoothSuccessiveIntegralInput_original (q : B) :
    smoothSuccessiveIntegralInput d hπ (modificationMap W (π ^ k) π d.b3 d.b4 d.b6 q) =
      algebraMap O L (f q) :=
  AlgHom.congr_fun (incidencePairFirst_original W (π ^ k) π d.b3 d.b4 d.b6 f g) q

/-- Every original modification function agrees before residue specialization on the output. -/
theorem smoothSuccessiveIntegralOutput_original (q : B) :
    smoothSuccessiveIntegralOutput d hπ (modificationMap W (π ^ k) π d.b3 d.b4 d.b6 q) =
      algebraMap O L (g q) :=
  AlgHom.congr_fun (incidencePairSecond_original W (π ^ k) π d.b3 d.b4 d.b6 f g) q

variable [IsLocalRing R] {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hk0 : 0 < k + 1) (hk : 2 * (k + 1) < depth)
local notation "C" => SmoothHorizontalResidueRing D
local notation "e₁" => smoothHorizontalIntegralFirstResidue d D hk0 hk hπ
local notation "e₂" => smoothHorizontalIntegralSecondResidue d D hk0 hk hπ

/-- The first actual branch has both units required by the common incidence refinement. -/
theorem successiveHorizontalOriginalFirst_units : IsUnit (e₁ (f t)) ∧ IsUnit (e₁ (g t)) := by
  change IsUnit (e₁ (smoothHorizontalIntegralInput d
    (successiveHorizontalEquationMap d hπ t))) ∧
    IsUnit (e₁ (smoothHorizontalIntegralOutput d
      (successiveHorizontalEquationMap d hπ t)))
  rw [successiveHorizontalEquationMap_t]
  exact smoothHorizontalIntegralFirstResidue_units d D hk0 hk hπ

/-- The opposite actual branch has both units on the same refinement. -/
theorem successiveHorizontalOriginalSecond_units : IsUnit (e₂ (f t)) ∧ IsUnit (e₂ (g t)) := by
  change IsUnit (e₂ (smoothHorizontalIntegralInput d
    (successiveHorizontalEquationMap d hπ t))) ∧
    IsUnit (e₂ (smoothHorizontalIntegralOutput d
      (successiveHorizontalEquationMap d hπ t)))
  rw [successiveHorizontalEquationMap_t]
  exact smoothHorizontalIntegralSecondResidue_units d D hk0 hk hπ

/-- The first original residue factors through the integral successive action refinement. -/
def smoothSuccessiveFirstIntegralResidue : L →ₐ[R] C :=
  incidencePairResidue W (π ^ k) π d.b3 d.b4 d.b6 f g e₁
    (successiveHorizontalOriginalFirst_units d hπ D hk0 hk).1
    (successiveHorizontalOriginalFirst_units d hπ D hk0 hk).2

/-- The opposite original residue factors through precisely the same integral refinement. -/
def smoothSuccessiveSecondIntegralResidue : L →ₐ[R] C :=
  incidencePairResidue W (π ^ k) π d.b3 d.b4 d.b6 f g e₂
    (successiveHorizontalOriginalSecond_units d hπ D hk0 hk).1
    (successiveHorizontalOriginalSecond_units d hπ D hk0 hk).2

/-- The first factorization preserves all functions of the original integral action source. -/
theorem smoothSuccessiveFirstIntegralResidue_base (q : O) :
    smoothSuccessiveFirstIntegralResidue d hπ D hk0 hk (algebraMap O L q) = e₁ q :=
  incidencePairResidue_base ..

/-- The opposite factorization also preserves every original action-source function. -/
theorem smoothSuccessiveSecondIntegralResidue_base (q : O) :
    smoothSuccessiveSecondIntegralResidue d hπ D hk0 hk (algebraMap O L q) = e₂ q :=
  incidencePairResidue_base ..

end FLT.Mazur.WeierstrassIntegralChart
