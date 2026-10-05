/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalAdditionComparison

/-!
# Formal parameters inside the group of points over a field

Embed the multivariate series ring in a field. The normalized formal chart gives
an injective map to Mathlib's actual group of projective points. At distinct
parameters it preserves the constructed addition, by the secant comparison.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] [IsDomain R] {σ : Type*}
variable {K : Type*} [Field K] (W : WeierstrassCurve R)
variable (f : MvPowerSeries σ R →+* K) (hf : Function.Injective f)

/-- The formal chart point after an injective embedding in a field. -/
noncomputable def fieldPoint (t : MvPowerSeries σ R) (ht : t.constantCoeff = 0) :
    ((curve W).map f).toProjective.Point :=
  ⟨(nonsingularLift_iff _).mpr
    ((map_nonsingular (curve W) hf _).mpr (nonsingular_representative W ht))⟩

/-- Equality of normalized projective points detects equality of parameters. -/
theorem fieldPoint_eq_iff {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    fieldPoint W f hf t ht = fieldPoint W f hf v hv ↔ t = v := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := Quotient.exact (congrArg Point.point h)
    have hy := congrFun hu 1
    have hx := congrFun hu 0
    have hu1 : (u : K) = 1 := by
      simpa [representative, Function.comp_apply, Units.smul_def] using hy
    apply hf
    simpa [representative, Function.comp_apply, Units.smul_def, hu1] using hx.symm
  · rintro rfl
    rfl

/-- The field group law agrees with formal addition at distinct parameters. -/
theorem fieldPoint_add_of_ne {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) (htv : t ≠ v) :
    fieldPoint W f hf (add W t v) (constantCoeff_add W ht hv) =
      fieldPoint W f hf t ht + fieldPoint W f hf v hv := by
  have hne : ¬ f ∘ representative W t ≈ f ∘ representative W v := by
    intro h
    apply htv
    apply (fieldPoint_eq_iff W f hf ht hv).mp
    exact Point.ext (Quotient.sound h)
  have he := congrArg (fun p : Fin 3 → MvPowerSeries σ R => f ∘ p)
    (addXYZ_representative W ht hv)
  rw [← map_addXYZ, comp_smul] at he
  have hs : IsUnit (f (additionScale W t v)) :=
    (show f (additionScale W t v) ≠ 0 from fun h =>
      additionScale_ne_zero W ht hv htv (hf (h.trans (map_zero f).symm))).isUnit
  apply Point.ext
  change (⟦f ∘ representative W (add W t v)⟧ : PointClass K) =
    ((curve W).map f).toProjective.addMap ⟦f ∘ representative W t⟧ ⟦f ∘ representative W v⟧
  rw [addMap_eq, add_of_not_equiv hne, he, smul_eq _ hs]

end FLT.Mazur.FormalInfinity
