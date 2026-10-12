/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicOriginalModuli
public import FLT.Mazur.AmpleCyclicClassEtale

/-!
# The etale-subgroup restriction of the full faithful chart

Every class reached by this chart has an etale cyclic subgroup. Consequently,
a modular object with a non-etale cyclic subgroup needs a different chart,
even if its underlying genus-one curve is smooth.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- Every original source family has an etale cyclic subgroup. -/
theorem cyclicSourceModuliClass_etale (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    ampleCyclicClassEtale (cyclicSourceModuliClass n f) :=
  (cyclicSourceCurve n f).relativeCyclicSubgroup_etale
    (cyclicSourceMarking n f) (cyclicSourceMarking_distinct n f)

/-- Forgetting full chart markings still lands among classes with etale subgroups. -/
theorem cyclicMarkedFamilyClassesToModuli_etale (q : CyclicMarkedFamilyClasses n T) :
    ampleCyclicClassEtale (cyclicMarkedFamilyClassesToModuli n q) := by
  induction q using Quotient.inductionOn with
  | h f => exact cyclicSourceModuliClass_etale n f

/-- Every point of the represented full slice has an etale modular subgroup. -/
theorem cyclicNormalizedSliceModuliMap_etale (f : T ⟶ cyclicNormalizedSlice n) :
    ampleCyclicClassEtale ((cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up f)) :=
  cyclicSourceModuliClass_etale n (f ≫ cyclicNormalizedSliceInclusion n)

/-- A non-etale cyclic level cannot admit a presentation by this full faithful slice. -/
theorem cyclicNormalizedSliceModuliMap_not_presentable (a : ampleCyclicLevels T n)
    (ha : ¬ Etale a.val.2.carrier.hom) :
    ¬ ∃ f : T ⟶ cyclicNormalizedSlice n,
      (cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up f) = Quotient.mk _ a := by
  rintro ⟨f, hf⟩
  have h := cyclicNormalizedSliceModuliMap_etale n f
  rw [hf] at h
  exact ha h

end FLT.Mazur.UniversalWeierstrass
