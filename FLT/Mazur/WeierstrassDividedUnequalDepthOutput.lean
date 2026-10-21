/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUnequalDepthSecant

/-!
# The unequal-depth secant in its actual divided target

The explicit quotient coordinates satisfy the equation at the difference
of the input depths. The resulting whole algebra map contracts to the
original secant, including where that original output is singular.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [Module.Flat R S] {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l) (z : Data W π (l - k))
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "T" => UnequalDepthSecantRing hπ d e hkl a c
local notation "c₀" => unequalDepthRight hπ d e hkl c
local notation "X" => unequalDepthSecantX hπ d e hkl a c
local notation "Y" => unequalDepthSecantY hπ d e hkl a c
local notation "t" => algebraMap R T (π ^ (l - k))
local notation "out" => dividedSecantOutput W (π ^ k) d.b3 d.b4 d.b6 a c₀
  d.factor3 d.factor4 d.factor6

/-- The target scale stays regular on the whole secant localization. -/
theorem unequalDepthSecant_regular : IsRegular t :=
  WeierstrassIntegralChart.flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ))

/-- The quotient coordinates satisfy the actual depth-difference equation. -/
theorem unequalDepthSecant_equation :
    Y ^ 2 + (algebraMap R T W.a₁ * X + algebraMap R T z.b3) * Y =
      t * X ^ 3 + algebraMap R T W.a₂ * X ^ 2 +
        algebraMap R T z.b4 * X + algebraMap R T z.b6 := by
  apply equation_of_scaled W (π ^ (l - k)) z.b3 z.b4 z.b6
    z.factor3 z.factor4 z.factor6 (unequalDepthSecant_regular hπ d e hkl a c) X Y
  rw [unequalDepthSecantX_scale, unequalDepthSecantY_scale]
  exact (Projective.equation_some ..).mpr
    (dividedSecant_equation W (π ^ k) d.b3 d.b4 d.b6 a c₀
      d.factor3 d.factor4 d.factor6)

/-- An actual algebra map into the depth-difference divided chart. -/
def unequalDepthSecantOutput : Coordinate W (π ^ (l - k)) z.b3 z.b4 z.b6 →ₐ[R] T :=
  evaluation W (π ^ (l - k)) z.b3 z.b4 z.b6 X Y
    (unequalDepthSecant_equation hπ d e hkl z a c)

local notation "o" => unequalDepthSecantOutput hπ d e hkl z a c

/-- The target abscissa is the explicitly computed quotient. -/
@[simp] theorem unequalDepthSecantOutput_x : o (x W (π ^ (l - k)) z.b3 z.b4 z.b6) = X :=
  evaluation_x ..

/-- The target ordinate is the explicitly computed quotient. -/
@[simp] theorem unequalDepthSecantOutput_y : o (y W (π ^ (l - k)) z.b3 z.b4 z.b6) = Y :=
  evaluation_y ..

/-- The complete original output algebra map is recovered by scaling both coordinates. -/
theorem unequalDepthSecantOutput_original :
    (o).comp (fromOriginal W (π ^ (l - k)) z.b3 z.b4 z.b6
      z.factor3 z.factor4 z.factor6) = out := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change o (fromOriginal W (π ^ (l - k)) z.b3 z.b4 z.b6
        z.factor3 z.factor4 z.factor6 (WeierstrassIntegralChart.coord W 2 0)) =
      out (WeierstrassIntegralChart.coord W 2 0)
    simp only [fromOriginal_x, map_mul, AlgHom.commutes,
      unequalDepthSecantOutput_x, dividedSecantOutput,
      WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_zero]
    exact unequalDepthSecantX_scale hπ d e hkl a c
  · change o (fromOriginal W (π ^ (l - k)) z.b3 z.b4 z.b6
        z.factor3 z.factor4 z.factor6 (WeierstrassIntegralChart.coord W 2 1)) =
      out (WeierstrassIntegralChart.coord W 2 1)
    simp only [fromOriginal_y, map_mul, AlgHom.commutes,
      unequalDepthSecantOutput_y, dividedSecantOutput,
      WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_one]
    exact unequalDepthSecantY_scale hπ d e hkl a c
  · change ((o).comp (fromOriginal W (π ^ (l - k)) z.b3 z.b4 z.b6
        z.factor3 z.factor4 z.factor6)) (WeierstrassIntegralChart.coord W 2 2) =
      out (WeierstrassIntegralChart.coord W 2 2)
    rw [WeierstrassIntegralChart.coord_self, map_one, map_one]

/-- The entire secant localization maps into the available difference-depth chart. -/
def unequalDepthSecantLift : Spec (.of T) ⟶ chart z :=
  Spec.map (CommRingCat.ofHom (o).toRingHom)

/-- The scheme-valued lift contracts to exactly the original secant formula. -/
@[reassoc] theorem unequalDepthSecantLift_contraction :
    unequalDepthSecantLift hπ d e hkl z a c ≫ toCurve z =
      dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
        d.factor3 d.factor4 d.factor6 := by
  unfold unequalDepthSecantLift toCurve WeierstrassDilatation.toCurve dividedSecantToCurve
  rw [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((o).comp
    (fromOriginal W (π ^ (l - k)) z.b3 z.b4 z.b6
      z.factor3 z.factor4 z.factor6)).toRingHom) ≫ _ = _
  rw [unequalDepthSecantOutput_original]

/-- The constructed output retains the original coefficient morphism. -/
@[reassoc] theorem unequalDepthSecantLift_structure :
    unequalDepthSecantLift hπ d e hkl z a c ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Coordinate W (π ^ (l - k)) z.b3 z.b4 z.b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
