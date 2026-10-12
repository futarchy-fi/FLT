/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredPoleLeadingCoefficient
public import FLT.Mazur.GenusOneGroupPoleBasis
public import FLT.Mazur.WeightedPoleCubicNormalization

/-!
# A Weierstrass equation from the original geometric group curve

Expanding the square of the actual pole-three function gives a weighted cubic.
Its leading coefficient is nonzero, and simultaneous scaling constructs genuine
Weierstrass coordinates on the original complement in every characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GenusOneGroupCoordinates
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)
  (hg : curveGenus G.hom hd hc = 1)
  (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker)

/-- Use the actual complement section ring on its bundled field module. -/
local instance equationFunctionRing : CommRing (divisorComplementModule G.hom s.left.ker) :=
  inferInstanceAs (CommRing
    Γ((Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl), ⊤))

local notation "x" => genusOneGroupPoleFunction G hd hc hg s hI 1 (by decide)
local notation "y" => genusOneGroupPoleFunction G hd hc hg s hI 2 (by decide)
local notation "P" => divisorPoleSubmodule G.hom hI
local notation "A" => divisorComplementModule G.hom s.left.ker

/-- The square of the original pole-three function in the sixth pole space. -/
def ySquare : P 6 := ⟨y ^ 2, by
  simpa only [pow_zero, one_mul] using product_mem G hd hc hg s hI 0 2⟩

/-- The actual unique coefficients of its monomial expansion. -/
def cubicCoefficients : Fin 6 → k :=
  (monomialBasis G hd hc hg s hI 6).repr (ySquare G hd hc hg s hI)

/-- The weighted cubic is an equality of the original complement functions. -/
theorem cubic_sum :
    ∑ j : Fin 6, cubicCoefficients G hd hc hg s hI j • monomial G hd hc hg s hI j =
      (ySquare G hd hc hg s hI : A) := by
  have he := FilteredPoleBasis.sum_repr_coe P
    (monomialBasis G hd hc hg s hI 6) (ySquare G hd hc hg s hI)
  simpa only [monomialBasis_apply, cubicCoefficients] using he

/-- The leading cubic coefficient cannot vanish because y² has exact order six. -/
theorem cubicCoefficients_last_ne_zero :
    cubicCoefficients G hd hc hg s hI (Fin.last 5) ≠ 0 := by
  apply FilteredPoleBasis.last_repr_ne_zero P (monomialBasis G hd hc hg s hI 6)
  · intro j
    rw [monomialBasis_apply]
    exact divisorPoleSubmodule_mono G.hom hI (WeightedPoleMonomials.order_le 5 j)
      (monomial_mem G hd hc hg s hI j)
  · simpa only [ySquare, pow_zero, one_mul] using
      product_not_mem G hd hc hg s hI 0 2 (by decide)

/-- Scalars on the original point complement come from its specified field morphism. -/
def scalar : k →+* A :=
  structureScalarMap ((Scheme.Opens.ι (X := G.left) s.left.ker.support.compl) ≫ G.hom)

/-- The equation is constructed from the original sixth-pole basis expansion. -/
def equation : WeierstrassCurve k :=
  WeightedPoleMonomials.cubicCurve (cubicCoefficients G hd hc hg s hI)

/-- Common nonzero scaling normalizes both leading terms without extracting roots. -/
def normalize (z : A) : A :=
  scalar G s (cubicCoefficients G hd hc hg s hI (Fin.last 5)) * z

/-- The normalization preserves all the original function information. -/
theorem normalize_injective : Function.Injective (normalize G hd hc hg s hI) :=
  WeightedPoleMonomials.scaled_coordinates_injective (scalar G s) _
    (cubicCoefficients_last_ne_zero G hd hc hg s hI)

/-- The constructed coordinates satisfy a Weierstrass equation over the original field. -/
theorem equation_holds : ((equation G hd hc hg s hI).map (scalar G s)).toAffine.Equation
    (normalize G hd hc hg s hI x) (normalize G hd hc hg s hI y) := by
  apply WeightedPoleMonomials.cubicCurve_equation
  have he := cubic_sum G hd hc hg s hI
  change ∑ j : Fin 6, cubicCoefficients G hd hc hg s hI j •
    WeightedPoleMonomials.monomial x y j = y ^ 2 at he
  rw [WeightedPoleMonomials.sum_six] at he
  have hsmul (a : k) (z : A) : a • z = scalar G s a * z := rfl
  simpa only [hsmul, mul_one] using he.symm

/-- Scaling keeps every original pole subspace, including exact orders two and three. -/
theorem normalize_mem_iff (z : A) (m : ℕ) :
    normalize G hd hc hg s hI z ∈ P m ↔ z ∈ P m :=
  Submodule.smul_mem_iff (P m) (cubicCoefficients_last_ne_zero G hd hc hg s hI)

end FLT.Mazur.GenusOneGroupCoordinates
