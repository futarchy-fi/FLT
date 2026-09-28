/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFilteredExtension
public import FLT.GroupScheme.RaynaudGenericSplitExtension

/-!
# Lifting generic splittings to integral models

A generic section of an integral projection extends uniquely when its source
has an order-three filtration. Faithfulness of the generic fibre proves the
integral section identity. A split generic extension of two order-three groups
therefore lifts to a splitting of the specified three-adic models, with both
inverse identities and the direct-sum decomposition holding integrally.

These results concern models over `ℤ_[3]`. They do not assert that an arbitrary
extension is generically split, or that a three-adic section descends to `ℤ[1/2]`.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsFractionRing R K]

/-- A splitting of two specified integral model maps, including the direct-sum
identity on the middle model. All identities hold on integral coordinate rings. -/
structure ModelSplitting {S X Q : FF R K} (i : ModelHom S X) (q : ModelHom X Q) where
  /-- Integral retraction onto the first summand. -/
  retraction : ModelHom X S
  /-- Integral section of the projection onto the second summand. -/
  sectionMap : ModelHom Q X
  /-- The retraction is a left inverse to the specified inclusion. -/
  retract : i.comp retraction = BialgHom.id R S.CoordinateRing
  /-- The section is a right inverse to the specified projection. -/
  sectionProjection : sectionMap.comp q = BialgHom.id R Q.CoordinateRing
  /-- The two summand projectors add to the integral identity. -/
  decomposition : ModelHom.add (retraction.comp i) (q.comp sectionMap) =
    BialgHom.id R X.CoordinateRing

/-- Restrict an integral splitting to the geometric generic fibre. -/
def ModelSplitting.toGenericSplitSequence {S X Q : FF R K}
    {i : ModelHom S X} {q : ModelHom X Q} (E : ModelSplitting i q) :
    GenericSplitSequence S X Q where
  inclusion := genericHom i
  retraction := genericHom E.retraction
  projection := genericHom q
  sectionMap := genericHom E.sectionMap
  retract x := by
    have h := congrArg (fun f : ModelHom S S ↦ genericHom f x) E.retract
    simpa only [genericHom_comp, genericHom_id] using h
  sectionProjection x := by
    have h := congrArg (fun f : ModelHom Q Q ↦ genericHom f x) E.sectionProjection
    simpa only [genericHom_comp, genericHom_id] using h
  decomposition x := by
    have h := congrArg (fun f : ModelHom X X ↦ genericHom f x) E.decomposition
    simpa only [ModelHom.genericHom_add, genericHom_comp, genericHom_id] using h

/-- Generic restriction determines an integral splitting uniquely. -/
theorem ModelSplitting.toGenericSplitSequence_injective {S X Q : FF R K}
    {i : ModelHom S X} {q : ModelHom X Q} :
    Function.Injective (ModelSplitting.toGenericSplitSequence (i := i) (q := q)) := by
  intro E F h
  have hr : E.retraction = F.retraction := genericHom_injective X S
    (congrArg GenericSplitSequence.retraction h)
  have hs : E.sectionMap = F.sectionMap := genericHom_injective Q X
    (congrArg GenericSplitSequence.sectionMap h)
  cases E
  cases F
  cases hr
  cases hs
  rfl

/-- A generic section from a filtered quotient extends uniquely to an integral
section of the specified projection. No filtration of the middle model is needed. -/
theorem ModelHom.existsUnique_section_of_orderThreeFiltration
    {X Q : FF ℤ_[3] ℚ_[3]} {n : ℕ} (q : ModelHom X Q)
    (hQ : Q.HasOrderThreeFiltration n) (s : GenericGaloisHom Q X)
    (hs : ∀ x, genericHom q (s x) = x) :
    ∃! sO : ModelHom Q X,
      genericHom sO = s ∧ sO.comp q = BialgHom.id ℤ_[3] Q.CoordinateRing := by
  obtain ⟨sO, hsO, hu⟩ :=
    raynaud_extend_generic_morphism_of_orderThreeFiltration Q X hQ s
  refine ⟨sO, ⟨hsO, ?_⟩, fun t ht ↦ hu t ht.1⟩
  apply genericHom_injective Q Q
  ext x
  simpa only [genericHom_comp, genericHom_id, hsO] using hs x

/-- A generic retraction from a filtered middle model extends uniquely to an
integral retraction of the specified inclusion. -/
theorem ModelHom.existsUnique_retraction_of_orderThreeFiltration
    {S X : FF ℤ_[3] ℚ_[3]} {n : ℕ} (i : ModelHom S X)
    (hX : X.HasOrderThreeFiltration n) (r : GenericGaloisHom X S)
    (hr : ∀ x, r (genericHom i x) = x) :
    ∃! rO : ModelHom X S,
      genericHom rO = r ∧ i.comp rO = BialgHom.id ℤ_[3] S.CoordinateRing := by
  obtain ⟨rO, hrO, hu⟩ :=
    raynaud_extend_generic_morphism_of_orderThreeFiltration X S hX r
  refine ⟨rO, ⟨hrO, ?_⟩, fun t ht ↦ hu t ht.1⟩
  apply genericHom_injective S S
  ext x
  simpa only [genericHom_comp, genericHom_id, hrO] using hr x

/-- A generic splitting lifts to the specified integral maps when the middle and
quotient models have order-three filtrations. The lifted splitting is unique. -/
theorem GenericSplitSequence.existsUnique_modelSplitting_of_orderThreeFiltration
    {S X Q : FF ℤ_[3] ℚ_[3]} {m n : ℕ} (E : GenericSplitSequence S X Q)
    (i : ModelHom S X) (q : ModelHom X Q)
    (hi : genericHom i = E.inclusion) (hq : genericHom q = E.projection)
    (hX : X.HasOrderThreeFiltration m) (hQ : Q.HasOrderThreeFiltration n) :
    ∃! EO : ModelSplitting i q, EO.toGenericSplitSequence = E := by
  obtain ⟨r, ⟨hr, hir⟩, _⟩ := i.existsUnique_retraction_of_orderThreeFiltration
    hX E.retraction (by simpa only [hi] using E.retract)
  obtain ⟨s, ⟨hs, hsq⟩, _⟩ := q.existsUnique_section_of_orderThreeFiltration
    hQ E.sectionMap (by simpa only [hq] using E.sectionProjection)
  have hd : ModelHom.add (r.comp i) (q.comp s) =
      BialgHom.id ℤ_[3] X.CoordinateRing := by
    apply genericHom_injective X X
    ext x
    simpa only [ModelHom.genericHom_add, genericHom_comp, genericHom_id, hr, hs, hi, hq]
      using E.decomposition x
  let EO : ModelSplitting i q := ⟨r, s, hir, hsq, hd⟩
  have hEO : EO.toGenericSplitSequence = E := by
    cases E
    simp only [ModelSplitting.toGenericSplitSequence, EO] at *
    cases hi
    cases hq
    cases hr
    cases hs
    rfl
  exact ⟨EO, hEO, fun F hF ↦
    ModelSplitting.toGenericSplitSequence_injective (hF.trans hEO.symm)⟩

/-- A split generic extension of order-three groups lifts uniquely to a splitting
of the chosen three-adic integral maps. No integral splitting is assumed. -/
theorem GenericSplitSequence.existsUnique_modelSplitting_of_order_three
    {S X Q : FF ℤ_[3] ℚ_[3]} (E : GenericSplitSequence S X Q)
    (i : ModelHom S X) (q : ModelHom X Q)
    (hi : genericHom i = E.inclusion) (hq : genericHom q = E.projection)
    (hS : Nat.card S.Points = 3) (hQ : Nat.card Q.Points = 3) :
    ∃! EO : ModelSplitting i q, EO.toGenericSplitSequence = E :=
  E.existsUnique_modelSplitting_of_orderThreeFiltration i q hi hq
    (E.hasOrderThreeFiltration hS hQ) (Q.hasOrderThreeFiltration_of_order_three hQ)

end ThreeAdicPlan
