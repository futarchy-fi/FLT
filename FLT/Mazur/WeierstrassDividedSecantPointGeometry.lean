/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairSecantEvaluation
public import FLT.Mazur.WeierstrassDividedPairSecantGeometry
public import FLT.Mazur.WeierstrassDividedSecantResidue
public import FLT.Mazur.WeierstrassProjectivePointSmooth

/-!
# Secant field points retain both inputs and have an originally smooth output

The universal divided secant factorization has the exact specified projections.
For opposite punctured branch residues its actual output lies in the original
relative smooth locus, without inverting the scale.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] K)
  (hu : IsUnit (a (x W s b3 b4 b6) - c (x W s b3 b4 b6)))
local notation "P" => DividedPairRing W s b3 b4 b6
local notation "T" => DividedPairSecantRing W s b3 b4 b6
local notation "L" => dividedPairLeft W s b3 b4 b6
local notation "M" => dividedPairRight W s b3 b4 b6
local notation "e" => dividedPairSecantEvaluation W s b3 b4 b6 a c hu
local notation "f" => Spec.map (CommRingCat.ofHom (e).toRingHom)
local notation "q" => Spec.map (CommRingCat.ofHom
  (algebraMap R (Coordinate W s b3 b4 b6)))

/-- The field-valued secant point retains the whole first divided input. -/
@[reassoc] theorem dividedSecantPoint_fst :
    f ≫ dividedPairSecantToProduct W s b3 b4 b6 ≫ pullback.fst q q =
      Spec.map (CommRingCat.ofHom a.toRingHom) := by
  rw [dividedPairSecantToProduct_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact dividedPairSecantEvaluation_left W s b3 b4 b6 a c hu z

/-- The same field-valued secant point retains the whole second divided input. -/
@[reassoc] theorem dividedSecantPoint_snd :
    f ≫ dividedPairSecantToProduct W s b3 b4 b6 ≫ pullback.snd q q =
      Spec.map (CommRingCat.ofHom c.toRingHom) := by
  rw [dividedPairSecantToProduct_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact dividedPairSecantEvaluation_right W s b3 b4 b6 a c hu z

/-- Opposite punctured divided branches give an actual originally smooth output morphism. -/
theorem dividedSecantPoint_output_range_smooth
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
    (hs : algebraMap R K s = 0) (h2 : algebraMap R K W.a₂ = 0)
    (ht : algebraMap R K W.a₁ ≠ 0)
    (ha : a (x W s b3 b4 b6) ≠ 0) (hc : c (x W s b3 b4 b6) ≠ 0)
    (hay : a (y W s b3 b4 b6) = 0)
    (hcy : c (y W s b3 b4 b6) = -algebraMap R K W.a₁ * c (x W s b3 b4 b6)) :
    Set.range (f ≫ dividedSecantToCurve W s b3 b4 b6 L M h3 h4 h6) ⊆
      WeierstrassIntegralChart.integralSmoothOpen W := by
  have heleft (z) : e ((IsScalarTower.toAlgHom R P T).comp L z) = a z :=
    dividedPairSecantEvaluation_left W s b3 b4 b6 a c hu z
  have heright (z) : e ((IsScalarTower.toAlgHom R P T).comp M z) = c z :=
    dividedPairSecantEvaluation_right W s b3 b4 b6 a c hu z
  have hn := dividedSecantOutput_residue_nonsingular W s b3 b4 b6 L M e h3 h4 h6
    hs h2 ht (by rwa [heleft]) (by rwa [heright])
    (by rwa [heleft]) (by rwa [heright, heright])
  let o := (e).comp (dividedSecantOutput W s b3 b4 b6 L M h3 h4 h6)
  have ho : o ∘ WeierstrassIntegralChart.coord W 2 =
      ![o (WeierstrassIntegralChart.coord W 2 0),
        o (WeierstrassIntegralChart.coord W 2 1), 1] := by
    funext i
    fin_cases i <;> simp
  have hp := WeierstrassIntegralChart.chartFieldPoint_range_smooth W 2 o
    (by rw [ho]; exact (Projective.nonsingular_some _ _).mpr hn)
  simpa only [dividedSecantToCurve, ← Category.assoc, ← Spec.map_comp,
    o, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp] using hp

end FLT.Mazur.WeierstrassDilatation
