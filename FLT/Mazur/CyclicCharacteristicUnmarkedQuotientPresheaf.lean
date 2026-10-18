/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicParameterPresheaf

/-!
# The exact pointwise unmarked quotient of the characteristic parameters

The quotient uses all genuine compatible comparisons, including those between
different characteristic charts. It embeds into the original modular-class
presheaf as precisely the classes admitting a global normalized parameter.
Every original smooth ample cyclic object belongs to this image fppf locally.
This constructs a quotient presheaf; it does not assert scheme representability.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual pointwise quotient by full unmarked compatible comparisons. -/
def unmarkedParameterClasses (T : Scheme) := Quotient (normalizedParameterSetoid n T)

/-- The quotient embeds into original modular classes by forgetting the parameter. -/
def unmarkedParameterClassMap (T : Scheme) : unmarkedParameterClasses n T →
    ampleCyclicClasses T n :=
  Quotient.lift (normalizedParameterClass n)
    (fun q r h ↦ (normalizedParameter_related_iff n q r).mp h)

/-- No two distinct unmarked parameter classes represent the same original modular object. -/
theorem unmarkedParameterClassMap_injective (T : Scheme) :
    Function.Injective (unmarkedParameterClassMap n T) := by
  intro q r
  induction q using Quotient.inductionOn with | h q =>
    induction r using Quotient.inductionOn with | h r =>
      intro h
      exact Quotient.sound ((normalizedParameter_related_iff n q r).mpr h)

/-- The image consists exactly of objects admitting a parameter in one actual chart. -/
theorem mem_unmarkedParameterClassMap_range_iff (T : Scheme) (z : ampleCyclicClasses T n) :
    z ∈ Set.range (unmarkedParameterClassMap n T) ↔
      ∃ (b : Bool) (q : T ⟶ normalizedLocus n b),
        (normalizedModuliMap n b).app (Opposite.op T) (ULift.up q) = z := by
  constructor
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with | h q =>
      exact ⟨q.1, q.2.down, hq⟩
  · rintro ⟨b, q, hq⟩
    exact ⟨Quotient.mk _ ⟨b, ULift.up q⟩, hq⟩

/-- The exact unmarked quotient is functorial under arbitrary base change. -/
def unmarkedParameterClassPresheaf : Schemeᵒᵖ ⥤ Type 1 where
  obj T := unmarkedParameterClasses n T.unop
  map g := ↾(Quotient.map ((normalizedParameterPresheaf n).map g)
    (fun _ _ h ↦ normalizedParameter_pullback_related n g.unop h))
  map_id T := by
    ext q
    induction q using Quotient.inductionOn with | h q =>
      change Quotient.mk _ ((normalizedParameterPresheaf n).map (𝟙 T) q) = Quotient.mk _ q
      rw [(normalizedParameterPresheaf n).map_id]
      rfl
  map_comp g h := by
    ext q
    induction q using Quotient.inductionOn with | h q =>
      change Quotient.mk _ ((normalizedParameterPresheaf n).map (g ≫ h) q) =
        Quotient.mk _ ((normalizedParameterPresheaf n).map h
          ((normalizedParameterPresheaf n).map g q))
      rw [(normalizedParameterPresheaf n).map_comp]
      rfl

/-- The injection of the full unmarked quotient into original modular classes is natural. -/
def unmarkedParameterModuliMap :
    unmarkedParameterClassPresheaf n ⟶ ampleCyclicClassPresheaf n where
  app T := ↾(unmarkedParameterClassMap n T.unop)
  naturality _ _ g := by
    ext q
    induction q using Quotient.inductionOn with | h q =>
      exact normalizedParameterClass_pullback n g.unop q

/-- Every original smooth ample cyclic class is in the exact quotient image fppf locally. -/
theorem exists_unmarkedParameterClass_fppf_cover {S : Scheme} {E : GeneralizedEllipticCurve S}
    [Smooth E.curve.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple) :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (z : ∀ i : C.I₀, unmarkedParameterClasses n (C.X i)),
      ∀ i, unmarkedParameterClassMap n (C.X i) (z i) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  obtain ⟨C, b, q, hq⟩ := exists_normalized_moduli_fppf_cover n H hc ha
  exact ⟨C, fun i ↦ Quotient.mk _ ⟨b i, ULift.up (q i)⟩, hq⟩

end FLT.Mazur.CyclicCharacteristicAtlas
