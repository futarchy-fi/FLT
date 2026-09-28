/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HenselianIdempotents
public import Mathlib.RingTheory.Artinian.Ring

/-!
# Primitive components of a Henselian algebra

When a Henselian pair has Artinian quotient, reduction to the product of the
residue fields lifts uniquely on idempotents. The coordinate idempotents of
that product lift to a complete orthogonal family of primitive idempotents.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {A : Type*} [CommRing A] (I : Ideal A)
variable [HenselianRing A I] [IsArtinianRing (A ⧸ I)]

/-- The simultaneous residue map of the special fibre. -/
def componentResidueMap : A →+* Π m : MaximalSpectrum (A ⧸ I), (A ⧸ I) ⧸ m.asIdeal :=
  (IsArtinianRing.quotNilradicalEquivPi (A ⧸ I)).toRingEquiv.toRingHom.comp
    ((Ideal.Quotient.mk (nilradical (A ⧸ I))).comp (Ideal.Quotient.mk I))

/-- Vanishing in every special-fibre residue field puts an element in the
integral Jacobson radical. -/
theorem componentResidueMap_ker_le_jacobson :
    RingHom.ker (componentResidueMap I) ≤ (⊥ : Ideal A).jacobson := by
  intro x hx
  change componentResidueMap I x = 0 at hx
  have hz : Ideal.Quotient.mk (nilradical (A ⧸ I)) (Ideal.Quotient.mk I x) = 0 := by
    apply (IsArtinianRing.quotNilradicalEquivPi (A ⧸ I)).injective
    change (IsArtinianRing.quotNilradicalEquivPi (A ⧸ I))
      (Ideal.Quotient.mk (nilradical (A ⧸ I)) (Ideal.Quotient.mk I x)) = 0 at hx
    simpa only [map_zero] using hx
  obtain ⟨n, hn⟩ := (mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hp : x ^ n ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
    exact hn
  rw [← (Ideal.isRadical_jacobson (⊥ : Ideal A)).radical]
  exact Ideal.mem_radical_iff.mpr ⟨n, HenselianRing.jac hp⟩

/-- Two integral idempotents agreeing in every residue field coincide. -/
theorem componentResidueMap_idempotent_ext {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : componentResidueMap I e = componentResidueMap I f) : e = f := by
  apply idempotent_eq_of_quotient_eq (RingHom.ker (componentResidueMap I))
    (componentResidueMap_ker_le_jacobson I) he hf
  rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, h, sub_self]

/-- Idempotents of the product of special-fibre residue fields lift uniquely. -/
theorem existsUnique_componentResidue_idempotent
    (e : Π m : MaximalSpectrum (A ⧸ I), (A ⧸ I) ⧸ m.asIdeal) (he : IsIdempotentElem e) :
    ∃! x : A, IsIdempotentElem x ∧ componentResidueMap I x = e := by
  let q := IsArtinianRing.quotNilradicalEquivPi (A ⧸ I)
  obtain ⟨b, hb, hbe⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk (nilradical (A ⧸ I)))
    (fun x hx ↦ mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx))
    (q.symm e) (Ideal.Quotient.mk_surjective _) (he.map q.symm.toRingEquiv.toRingHom)
  obtain ⟨a, ha, _⟩ := existsUnique_idempotent_lift I b hb
  have hae : componentResidueMap I a = e := by
    change q (Ideal.Quotient.mk (nilradical (A ⧸ I)) (Ideal.Quotient.mk I a)) = e
    rw [ha.2, hbe, q.apply_symm_apply]
  exact ⟨a, ⟨ha.1, hae⟩, fun x hx ↦
    componentResidueMap_idempotent_ext I hx.1 ha.1 (hx.2.trans hae.symm)⟩

/-- A special fibre has finitely many maximal ideals. -/
local instance componentIndexFintype : Fintype (MaximalSpectrum (A ⧸ I)) := Fintype.ofFinite _
/-- Classical equality for indexing the residue-field product. -/
local instance componentIndexDecidableEq : DecidableEq (MaximalSpectrum (A ⧸ I)) :=
  Classical.decEq _

/-- The integral idempotent of the component indexed by a special-fibre maximal ideal. -/
def componentIdempotent (m : MaximalSpectrum (A ⧸ I)) : A :=
  (existsUnique_componentResidue_idempotent I (Pi.single m 1)
    ((CompleteOrthogonalIdempotents.single fun n : MaximalSpectrum (A ⧸ I) ↦
      (A ⧸ I) ⧸ n.asIdeal).idem m)).choose

/-- Component elements are idempotent. -/
theorem componentIdempotent_isIdempotent (m : MaximalSpectrum (A ⧸ I)) :
    IsIdempotentElem (componentIdempotent I m) :=
  (existsUnique_componentResidue_idempotent I (Pi.single m 1)
    ((CompleteOrthogonalIdempotents.single fun n : MaximalSpectrum (A ⧸ I) ↦
      (A ⧸ I) ⧸ n.asIdeal).idem m)).choose_spec.1.1

/-- A component is one in its own residue field and zero in the others. -/
@[simp] theorem componentIdempotent_residue (m : MaximalSpectrum (A ⧸ I)) :
    componentResidueMap I (componentIdempotent I m) = Pi.single m 1 :=
  (existsUnique_componentResidue_idempotent I (Pi.single m 1)
    ((CompleteOrthogonalIdempotents.single fun n : MaximalSpectrum (A ⧸ I) ↦
      (A ⧸ I) ⧸ n.asIdeal).idem m)).choose_spec.1.2

/-- All primitive components together give a complete orthogonal family. -/
theorem componentIdempotent_complete : CompleteOrthogonalIdempotents (componentIdempotent I) := by
  have ho : OrthogonalIdempotents (componentIdempotent I) := by
    refine ⟨componentIdempotent_isIdempotent I, fun m n hmn ↦ ?_⟩
    apply componentResidueMap_idempotent_ext I
      ((componentIdempotent_isIdempotent I m).mul (componentIdempotent_isIdempotent I n)) .zero
    simp only [map_mul, componentIdempotent_residue, map_zero]
    exact (CompleteOrthogonalIdempotents.single fun n : MaximalSpectrum (A ⧸ I) ↦
      (A ⧸ I) ⧸ n.asIdeal).ortho hmn
  refine ⟨ho, ?_⟩
  apply componentResidueMap_idempotent_ext I ho.isIdempotentElem_sum .one
  simpa only [map_sum, componentIdempotent_residue, map_one] using
    (CompleteOrthogonalIdempotents.single fun n : MaximalSpectrum (A ⧸ I) ↦
      (A ⧸ I) ⧸ n.asIdeal).complete

/-- No component can be split by a nontrivial integral idempotent. -/
theorem componentIdempotent_primitive (m : MaximalSpectrum (A ⧸ I))
    {d : A} (hd : IsIdempotentElem d) (hm : d * componentIdempotent I m = d) :
    d = 0 ∨ d = componentIdempotent I m := by
  let : Field ((A ⧸ I) ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have hdi : IsIdempotentElem (componentResidueMap I d m) :=
    (hd.map (componentResidueMap I)).map (Pi.evalRingHom _ m)
  have hother (n : MaximalSpectrum (A ⧸ I)) (hn : n ≠ m) : componentResidueMap I d n = 0 := by
    have hh := congrArg (fun x : A ↦ componentResidueMap I x n) hm
    simpa [map_mul, Pi.single_eq_of_ne hn] using hh.symm
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hdi with hzero | hone
  · left
    apply componentResidueMap_idempotent_ext I hd .zero
    ext n
    by_cases hn : n = m
    · subst n; simpa using hzero
    · simpa using hother n hn
  · right
    apply componentResidueMap_idempotent_ext I hd (componentIdempotent_isIdempotent I m)
    rw [componentIdempotent_residue]
    ext n
    by_cases hn : n = m
    · subst n; simpa using hone
    · simp [hother n hn, Pi.single_eq_of_ne hn]

/-- The product decomposition into primitive integral component algebras. -/
def primitiveComponentEquiv {R : Type*} [CommRing R] [Algebra R A] :
    A ≃ₐ[R] Π m : MaximalSpectrum (A ⧸ I), A ⧸ Ideal.span {1 - componentIdempotent I m} :=
  AlgEquiv.ofBijective (AlgHom.pi fun m ↦ Ideal.Quotient.mkₐ R
    (Ideal.span {1 - componentIdempotent I m})) (componentIdempotent_complete I).bijective_pi

/-- Each component factor has only the zero and unit idempotents, the algebraic
criterion for connectedness of its spectrum. -/
theorem componentFactor_idempotent_trivial (m : MaximalSpectrum (A ⧸ I))
    (d : A ⧸ Ideal.span {1 - componentIdempotent I m}) (hd : IsIdempotentElem d) :
    d = 0 ∨ d = 1 := by
  let e := componentIdempotent I m
  have he : IsIdempotentElem e := componentIdempotent_isIdempotent I m
  let E := AlgEquiv.prodQuotientOfIsIdempotentElem A he.one_sub he
    (sub_add_cancel 1 e) he.one_sub_mul_self
  let a := E.symm (d, 0)
  have ha : IsIdempotentElem a := by
    apply IsIdempotentElem.map _ E.symm.toRingEquiv.toRingHom
    exact Prod.ext hd.eq (by simp)
  have hEe : E e = (1, 0) := by
    apply Prod.ext
    · change Ideal.Quotient.mk (Ideal.span {1 - e}) e = 1
      have hh : Ideal.Quotient.mk (Ideal.span {1 - e}) (1 - e) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      exact (sub_eq_zero.mp (by simpa only [map_sub, map_one] using hh)).symm
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hae : a * e = a := by
    apply E.injective
    rw [map_mul, hEe]
    simp only [a, E.apply_symm_apply, Prod.mk_mul_mk, mul_one, mul_zero]
  rcases componentIdempotent_primitive I m ha hae with hzero | hone
  · left
    have hh := congrArg (fun x ↦ (E x).1) hzero
    simpa [a] using hh
  · right
    have hh := congrArg (fun x ↦ (E x).1) hone
    change (E a).1 = (E e).1 at hh
    simpa only [a, E.apply_symm_apply, hEe] using hh

end ThreeAdicPlan
