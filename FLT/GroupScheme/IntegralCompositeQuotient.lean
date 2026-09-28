/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.IntegralClosedImmersion
public import FLT.GroupScheme.IntegralQuotientDescent

/-!
# The quotient by a composite integral subgroup

Two nested kernels give a quotient of the original middle model by the
innermost kernel. Descent constructs the maps from the original intermediate
quotient and to the original outer quotient, retaining their commuting formulas.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [IsDedekindDomain R] [IsPrincipalIdealRing R]

/-- Quotient a model by two composed closed subgroup inclusions, retaining the
specified kernel and both compatible integral maps between the quotient models. -/
theorem existsCompositeIntegralQuotient
    {A B C H Q : FiniteFlatObject R}
    (E₁ : FiniteFlatExtension A B C) (E₂ : FiniteFlatExtension B H Q) :
    ∃ T : FiniteFlatObject R, ∃ E : FiniteFlatExtension A H T,
      ∃ i : C.Hom T, ∃ q : T.Hom Q,
        E.inclusion = E₁.inclusion.comp E₂.inclusion ∧
        E₁.quotient.comp i = E₂.inclusion.comp E.quotient ∧
        E.quotient.comp q = E₂.quotient := by
  let f : A.Hom H := E₁.inclusion.comp E₂.inclusion
  have hi : Function.Injective (FiniteFlatObject.pointMap f) := by
    intro a b hab
    apply E₁.pointsInjective
    apply E₂.pointsInjective
    simpa only [f, FiniteFlatObject.pointMap_comp] using hab
  have hf : Function.Surjective f := E₁.inclusion_surjective.comp E₂.inclusion_surjective
  let j : GenericGaloisHom A.toFF H.toFF := genericHom f
  obtain ⟨T₀, q₀, hq₀, hexact, _⟩ := j.exists_exact_quotient
  let T := (q₀.flatQuotient hq₀).toFiniteFlatObject
  let E : FiniteFlatExtension A H T :=
    FiniteFlatObject.extensionOfClosedImmersion f hi hf q₀ hq₀ hexact
  have hE : E.inclusion = f :=
    FiniteFlatObject.extensionOfClosedImmersionInclusion f hi hf q₀ hq₀ hexact
  have hk : E₁.inclusion.toAlgHom.comp
      (E₂.inclusion.comp E.quotient).toAlgHom =
      (Algebra.ofId R A.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R T.model.CoordinateRing) := by
    change f.toAlgHom.comp E.quotient.toAlgHom = _
    rw [← hE]
    exact E.compositionZero
  let i : C.Hom T := E₁.descendHom (E₂.inclusion.comp E.quotient) hk
  have hq : E.inclusion.toAlgHom.comp E₂.quotient.toAlgHom =
      (Algebra.ofId R A.model.CoordinateRing).comp
        (Bialgebra.counitAlgHom R Q.model.CoordinateRing) := by
    rw [hE]
    change E₁.inclusion.toAlgHom.comp
      (E₂.inclusion.toAlgHom.comp E₂.quotient.toAlgHom) = _
    rw [E₂.compositionZero]
    ext x
    exact E₁.inclusion.toAlgHom.commutes _
  exact ⟨T, E, i, E.descendHom E₂.quotient hq, hE,
    E₁.descendHomComp _ hk, E.descendHomComp _ hq⟩

omit [IsFractionRing R ℚ] [IsDedekindDomain R] [IsPrincipalIdealRing R] in
/-- The compatible composite quotient diagram is exact on geometric points. -/
theorem compositeIntegralQuotientPointsExact
    {A B C H Q T : FiniteFlatObject R}
    (E₁ : FiniteFlatExtension A B C) (E₂ : FiniteFlatExtension B H Q)
    (E : FiniteFlatExtension A H T) (i : C.Hom T) (q : T.Hom Q)
    (hi : E.inclusion = E₁.inclusion.comp E₂.inclusion)
    (hc : E₁.quotient.comp i = E₂.inclusion.comp E.quotient)
    (hq : E.quotient.comp q = E₂.quotient) :
    Function.Injective (FiniteFlatObject.pointMap i) ∧
      Function.Surjective (FiniteFlatObject.pointMap q) ∧
      ∀ t, FiniteFlatObject.pointMap q t = 0 ↔
        ∃ c, FiniteFlatObject.pointMap i c = t := by
  have hiA (a : A.points) : FiniteFlatObject.pointMap E.inclusion a =
      FiniteFlatObject.pointMap E₂.inclusion (FiniteFlatObject.pointMap E₁.inclusion a) := by
    rw [hi, FiniteFlatObject.pointMap_comp]
  have hiC (b : B.points) :
      FiniteFlatObject.pointMap i (FiniteFlatObject.pointMap E₁.quotient b) =
        FiniteFlatObject.pointMap E.quotient (FiniteFlatObject.pointMap E₂.inclusion b) := by
    simpa only [FiniteFlatObject.pointMap_comp] using
      congrArg (fun f : B.Hom T ↦ FiniteFlatObject.pointMap f b) hc
  have hqH (h : H.points) :
      FiniteFlatObject.pointMap q (FiniteFlatObject.pointMap E.quotient h) =
        FiniteFlatObject.pointMap E₂.quotient h := by
    simpa only [FiniteFlatObject.pointMap_comp] using
      congrArg (fun f : H.Hom Q ↦ FiniteFlatObject.pointMap f h) hq
  refine ⟨?_, ?_, ?_⟩
  · apply (injective_iff_map_eq_zero (FiniteFlatObject.pointMap i)).mpr
    intro c hc0
    obtain ⟨b, rfl⟩ := E₁.pointsSurjective c
    obtain ⟨a, ha⟩ := (E.pointsExact (FiniteFlatObject.pointMap E₂.inclusion b)).mp
      ((hiC b).symm.trans hc0)
    have hb : FiniteFlatObject.pointMap E₁.inclusion a = b :=
      E₂.pointsInjective ((hiA a).symm.trans ha)
    exact (E₁.pointsExact b).mpr ⟨a, hb⟩
  · intro q'
    obtain ⟨h, hh⟩ := E₂.pointsSurjective q'
    exact ⟨FiniteFlatObject.pointMap E.quotient h, (hqH h).trans hh⟩
  · intro t
    constructor
    · intro ht
      obtain ⟨h, rfl⟩ := E.pointsSurjective t
      obtain ⟨b, hb⟩ := (E₂.pointsExact h).mp ((hqH h).symm.trans ht)
      exact ⟨FiniteFlatObject.pointMap E₁.quotient b,
        (hiC b).trans (congrArg (FiniteFlatObject.pointMap E.quotient) hb)⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨b, rfl⟩ := E₁.pointsSurjective c
      rw [hiC, hqH]
      exact (E₂.pointsExact _).mpr ⟨b, rfl⟩

end ThreeAdicPlan
