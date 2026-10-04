/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousHilbert90
public import FLT.GaloisRepresentation.Extensions.ContinuousCup
public import FLT.GroupScheme.AlgebraicClosureKummer
public import FLT.GroupScheme.RootModuleLinear

/-!
# Reflection of two-boundaries by root coefficient inclusion

Hilbert 90 makes the multiple of a field-unit bounding cochain principal.
A root of its principal element corrects the cochain into roots of unity.
Thus coefficient inclusion reflects vanishing, without a comparison premise.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open KummerTheory GaloisRepresentation.Extensions

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  [IsAlgClosed C] [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)]
  (n : ℕ) [NeZero n]

attribute [local instance] fieldUnitAction

/-- Root coefficients included additively into field units. -/
def rootCoefficientInclusion : RootModule C n →+ Additive Cˣ where
  toFun x := Additive.ofMul (rootUnit x)
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsGalois K C] [IsAlgClosed C] [TopologicalSpace (Additive Cˣ)]
  [DiscreteTopology (Additive Cˣ)] [NeZero n] in
/-- The inclusion commutes with the actual Galois actions. -/
theorem rootCoefficientInclusion_smul (g : Gal(C/K)) (x : RootModule C n) :
    rootCoefficientInclusion C n (g • x) = g • rootCoefficientInclusion C n x := rfl

/-- Inclusion of a root-valued continuous two-cochain. -/
def includedRootTwoCochain (c : C(Gal(C/K) × Gal(C/K), RootModule C n)) :
    C(Gal(C/K) × Gal(C/K), Additive Cˣ) :=
  ⟨fun z => rootCoefficientInclusion C n (c z), continuous_of_discreteTopology.comp c.continuous⟩

/-- A field-unit bounding cochain can be corrected to have root-of-unity values. -/
theorem rootCoefficient_boundary_reflects
    (c : C(Gal(C/K) × Gal(C/K), RootModule C n))
    (b : C(Gal(C/K), Additive Cˣ))
    (hb : ∀ g h, g • b h - b (g * h) + b g = includedRootTwoCochain K C n c (g, h)) :
    ContinuousIsCoboundaryTwo c := by
  let i := rootCoefficientInclusion C n
  have hn (x : RootModule C n) : n • i x = 0 := by
    rw [← map_nsmul, rootModule_p_nsmul, map_zero]
  let z : ContinuousCocycle Gal(C/K) (Additive Cˣ) :=
    ⟨⟨fun g => n • b g, b.continuous.const_smul n⟩, fun g h => by
      have he := congrArg (fun a : Additive Cˣ => n • a) (hb g h)
      change _ = n • i (c (g, h)) at he
      rw [hn, smul_add, smul_sub, smul_comm n] at he
      change n • b (g * h) = g • (n • b h) + n • b g
      apply eq_of_sub_eq_zero
      calc
        n • b (g * h) - (g • (n • b h) + n • b g) =
            -(g • (n • b h) - n • b (g * h) + n • b g) := by abel
        _ = 0 := by rw [he, neg_zero]⟩
  obtain ⟨a, ha⟩ := continuousFieldUnitCocycle_eq_coboundary K C z
  obtain ⟨r, hr⟩ := exists_unit_root (K := C) (L := C) (n := n) (Additive.toMul a)
  have hr' : n • Additive.ofMul r = a := by
    apply Additive.toMul.injective
    simpa using hr
  let t : C(Gal(C/K), Additive Cˣ) :=
    ⟨fun g => b g - (g • Additive.ofMul r - Additive.ofMul r),
      b.continuous.sub ((continuous_id.smul continuous_const).sub continuous_const)⟩
  have ht (g : Gal(C/K)) : n • t g = 0 := by
    change n • (b g - (g • Additive.ofMul r - Additive.ofMul r)) = 0
    rw [smul_sub, smul_sub, smul_comm n, hr']
    exact sub_eq_zero.mpr (ha g)
  let lift : {v : Additive Cˣ // n • v = 0} → RootModule C n := fun v =>
    Additive.ofMul ⟨Additive.toMul v.val, congrArg Additive.toMul v.property⟩
  let d : C(Gal(C/K), RootModule C n) :=
    ⟨fun g => lift ⟨t g, ht g⟩,
      (continuous_of_discreteTopology (f := lift)).comp (t.continuous.subtype_mk ht)⟩
  have hd (g : Gal(C/K)) : i (d g) = t g := rfl
  refine ⟨d, fun g h => ?_⟩
  apply Additive.ofMul.injective.comp rootUnit_injective
  change i (g • d h - d (g * h) + d g) = i (c (g, h))
  rw [map_add, map_sub, rootCoefficientInclusion_smul, hd, hd, hd]
  change g • (b h - (h • Additive.ofMul r - Additive.ofMul r)) -
    (b (g * h) - ((g * h) • Additive.ofMul r - Additive.ofMul r)) +
      (b g - (g • Additive.ofMul r - Additive.ofMul r)) = _
  simp only [smul_sub, mul_smul]
  have he := hb g h
  change g • b h - b (g * h) + b g = i (c (g, h)) at he
  rw [← he]
  abel

/-- Root coefficient inclusion preserves and reflects continuous two-boundaries. -/
theorem includedRootTwoCochain_coboundary_iff
    (c : C(Gal(C/K) × Gal(C/K), RootModule C n)) :
    ContinuousIsCoboundaryTwo (includedRootTwoCochain K C n c) ↔
      ContinuousIsCoboundaryTwo c := by
  constructor
  · rintro ⟨b, hb⟩
    exact rootCoefficient_boundary_reflects K C n c b hb
  · rintro ⟨b, hb⟩
    refine ⟨⟨fun g => rootCoefficientInclusion C n (b g),
      continuous_of_discreteTopology.comp b.continuous⟩, fun g h => ?_⟩
    have he := congrArg (rootCoefficientInclusion C n) (hb g h)
    change g • rootCoefficientInclusion C n (b h) -
      rootCoefficientInclusion C n (b (g * h)) + rootCoefficientInclusion C n (b g) =
        rootCoefficientInclusion C n (c (g, h))
    simpa only [map_add, map_sub, rootCoefficientInclusion_smul] using he

end LocalClassFieldTheory
