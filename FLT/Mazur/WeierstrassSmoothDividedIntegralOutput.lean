/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothDividedSecantSource
public import FLT.Mazur.WeierstrassDilatationLifting
public import FLT.Mazur.WeierstrassDilatationOriginalQuotients

/-!
# Constructing the actual integral divided output

Center containment makes both original output coordinates divisible by the scale.
Regularity on the concrete secant source constructs a unique divided output with
exactly the original ordinary addition as its contraction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : WeierstrassDividedDepth.Data W π k)
local notation "H" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "T" => SmoothDividedSecantRing d
local notation "f" => smoothDividedSecantPresentation d
local notation "orig" => WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6

/-- The actual divided secant input principalizes the full original center. -/
theorem smoothDividedSecantInput_center :
    (modificationChartCenter W (π ^ k) 2).map
        ((f).comp (ordinaryInputRight W false)).toRingHom =
      Ideal.span {algebraMap R T (π ^ k)} := by
  have h := WeierstrassDilatation.originalDividedPoint_center W (π ^ k)
    d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
    ((f).comp (ordinaryInputRight W false)) (AlgHom.id R T)
    (smoothDividedSecantInput d) (by
      simpa only [AlgHom.id_comp] using smoothDividedSecantInput_original d)
  change Ideal.map (RingHom.id T) _ = _ at h
  simpa only [Ideal.map_id] using h

/-- Both original output coordinates are divisible on the constructed ordinary source. -/
theorem smoothDividedSecantOutput_divisible :
    algebraMap R T (π ^ k) ∣ smoothDividedSecantOutput d (coord W 2 0) ∧
      algebraMap R T (π ^ k) ∣ smoothDividedSecantOutput d (coord W 2 1) := by
  have h := ordinarySpecialization_center_le W (π ^ k) false f
    d.b3 d.b4 d.factor3 d.factor4
  rw [smoothDividedSecantInput_center] at h
  have hcoord := (modificationChartCenter_map_le_iff W (π ^ k) 2
    (smoothDividedSecantOutput d) (Ideal.span {algebraMap R T (π ^ k)})).mp h
  exact ⟨Ideal.mem_span_singleton.mp hcoord.2.1, Ideal.mem_span_singleton.mp hcoord.2.2⟩

variable (hs : IsRegular (π ^ k))
include hs

/-- The genuine ordinary output has a unique integral divided lift. -/
theorem smoothDividedIntegralOutput_existsUnique :
    ∃! M : H →ₐ[R] T, M.comp orig = smoothDividedSecantOutput d :=
  (WeierstrassDilatation.existsUnique_lift_iff W (π ^ k) d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6 (smoothDividedSecant_base_regular d hs)
    (smoothDividedSecantOutput d)).mpr (smoothDividedSecantOutput_divisible d)

/-- The divided output constructed from the actual center and regular original scale. -/
def smoothDividedIntegralOutput : H →ₐ[R] T :=
  (smoothDividedIntegralOutput_existsUnique d hs).exists.choose

/-- The output lift retains the entire original cubic algebra map. -/
theorem smoothDividedIntegralOutput_original :
    (smoothDividedIntegralOutput d hs).comp orig = smoothDividedSecantOutput d :=
  (smoothDividedIntegralOutput_existsUnique d hs).exists.choose_spec

/-- Its divided horizontal coordinate multiplies to the actual ordinary output. -/
theorem smoothDividedIntegralOutput_x :
    algebraMap R T (π ^ k) *
        smoothDividedIntegralOutput d hs (WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6) =
      smoothDividedSecantOutput d (coord W 2 0) := by
  have h := congrArg (fun g => g (coord W 2 0)) (smoothDividedIntegralOutput_original d hs)
  simpa only [AlgHom.comp_apply, WeierstrassDilatation.fromOriginal_x,
    map_mul, AlgHom.commutes] using h

/-- Its divided vertical coordinate multiplies to the actual ordinary output. -/
theorem smoothDividedIntegralOutput_y :
    algebraMap R T (π ^ k) *
        smoothDividedIntegralOutput d hs (WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6) =
      smoothDividedSecantOutput d (coord W 2 1) := by
  have h := congrArg (fun g => g (coord W 2 1)) (smoothDividedIntegralOutput_original d hs)
  simpa only [AlgHom.comp_apply, WeierstrassDilatation.fromOriginal_y,
    map_mul, AlgHom.commutes] using h

end FLT.Mazur.WeierstrassIntegralChart
