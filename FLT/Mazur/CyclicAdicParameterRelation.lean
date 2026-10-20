/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicAdicParameters

/-!
# Full comparisons on the enlarged characteristic and adic parameter functor

The relation consists of actual compatible isomorphisms of the entire pulled
back curve and subgroup. It includes every mixed comparison and is stable under
arbitrary base change. This constructs the relation on tests, not its representing scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicAdicParameters
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Genuine compatible comparisons of the full original pulled-back levels. -/
def Related {T : Scheme} (q r : Parameter n T) : Prop :=
  Nonempty (CompatibleIso (parameterLevel n q).val.2 (parameterLevel n r).val.2)

/-- The relation is exactly the kernel of the original modular-class transformation. -/
theorem related_iff_class_eq {T : Scheme} (q r : Parameter n T) :
    Related n q r ↔ parameterClass n q = parameterClass n r := by
  constructor
  · intro h
    exact Quotient.sound h
  · intro h
    exact Quotient.exact h

/-- Full identity comparisons make the relation reflexive. -/
theorem related_refl {T : Scheme} (q : Parameter n T) : Related n q q :=
  ⟨CompatibleIso.refl _⟩

/-- Full compatible isomorphisms can be reversed. -/
theorem Related.symm {T : Scheme} {q r : Parameter n T} (h : Related n q r) :
    Related n r q := h.map CompatibleIso.symm

/-- The middle chart can be smooth or adic when compatible comparisons compose. -/
theorem Related.trans {T : Scheme} {q r s : Parameter n T}
    (h : Related n q r) (k : Related n r s) : Related n q s := by
  obtain ⟨a⟩ := h
  obtain ⟨b⟩ := k
  exact ⟨a.trans b⟩

/-- Restrict the actual comparison, retaining canonical iterated base-change maps. -/
theorem Related.baseChange {T U : Scheme} {q r : Parameter n T}
    (h : Related n q r) (g : U ⟶ T) :
    Related n ((parameterPresheaf n).map g.op q) ((parameterPresheaf n).map g.op r) := by
  obtain ⟨a⟩ := h
  exact ⟨(compatibleBaseChangeComp (chartLevel n q.1).val.2 q.2.down g).trans
    ((a.baseChange g).trans
      (compatibleBaseChangeComp (chartLevel n r.1).val.2 r.2.down g).symm)⟩

/-- The actual full comparison relation on all three chart choices. -/
def parameterSetoid (T : Scheme) : Setoid (Parameter n T) where
  r := Related n
  iseqv := ⟨related_refl n, Related.symm n, Related.trans n⟩

/-- On the original smooth parameters, no comparison has been added or removed. -/
theorem smooth_related_iff {T : Scheme}
    (q r : CyclicCharacteristicAtlas.NormalizedParameter n T) :
    Related n ((smoothInclusion n).app (Opposite.op T) q)
      ((smoothInclusion n).app (Opposite.op T) r) ↔
        (CyclicCharacteristicAtlas.normalizedParameterSetoid n T).r q r := Iff.rfl

/-- Any two parameters for the same original object agree on every common test. -/
theorem related_overlap {S T U V : Scheme} (z : ampleCyclicClasses S n)
    (f : T ⟶ S) (g : U ⟶ S) (q : Parameter n T) (r : Parameter n U)
    (hq : parameterClass n q = ampleCyclicClassesPullback f n z)
    (hr : parameterClass n r = ampleCyclicClassesPullback g n z)
    (a : V ⟶ T) (b : V ⟶ U) (hab : a ≫ f = b ≫ g) :
    Related n ((parameterPresheaf n).map a.op q) ((parameterPresheaf n).map b.op r) := by
  apply (related_iff_class_eq n _ _).mpr
  rw [parameterClass_pullback, parameterClass_pullback, hq, hr]
  exact (congrFun (ampleCyclicClassesPullback_comp f a n) z).symm.trans
    ((congrArg (fun k ↦ ampleCyclicClassesPullback k n z) hab).trans
      (congrFun (ampleCyclicClassesPullback_comp g b n) z))

end FLT.Mazur.CyclicAdicParameters
