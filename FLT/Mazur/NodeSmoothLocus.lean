/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeInfinitesimalObstruction

/-!
# The exact smooth loci of the polygon node charts

The punctures are smooth and the omitted origins have infinitesimal
obstructions. This identifies both the algebra and scheme smooth loci.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.StructureSheaf Polynomial

namespace FLT.Mazur.PolygonNodePresentation

open PolygonNodeEqualizer PolygonNodeLocalization

universe u

variable {K : Type u} [Field K]

/-- A prime containing the generators contains the kernel of evaluation at zero. -/
theorem ker_le_of_present {S : Type*} [CommRing S] [Algebra K S]
    (f : MvPolynomial (Fin 2) K →ₐ[K] S) (hf : Function.Surjective f)
    (e : S →ₐ[K] K) (P : Ideal S)
    (he : ∀ i, e (f (MvPolynomial.X i)) = 0)
    (hP : ∀ i, f (MvPolynomial.X i) ∈ P) : RingHom.ker e.toRingHom ≤ P := by
  let q := Ideal.Quotient.mkₐ K P
  have h : q = (Algebra.ofId K (S ⧸ P)).comp e := by
    apply (AlgHom.cancel_right hf).mp
    ext i
    simp only [AlgHom.comp_apply, he, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hP i)
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hz' : e z = 0 := hz
  simpa only [AlgHom.comp_apply, hz', map_zero, q, Ideal.Quotient.mkₐ_eq_mk] using
    AlgHom.congr_fun h z

/-- Vanishing of both branch coordinates cuts out precisely the closed origin. -/
theorem a_zeroLocus : PrimeSpectrum.zeroLocus {x (R := K), y} =
    PrimeSpectrum.zeroLocus (RingHom.ker (aEval (R := K)).toRingHom) := by
  ext p
  constructor
  · intro hp
    apply ker_le_of_present aPresent aPresent_surjective aEval p.asIdeal
    · intro i; fin_cases i <;> simp [aEval]
    · intro i; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one,
        aPresent_X_zero, aPresent_X_one] <;> exact hp (by simp)
  · intro hp z hz
    apply hp
    rcases hz with rfl | hz
    · simp [RingHom.mem_ker, aEval]
    · rcases hz with rfl
      simp [RingHom.mem_ker, aEval]

/-- The conductor vanishes only at the closed origin of the one-gon chart. -/
theorem b_zeroLocus : PrimeSpectrum.zeroLocus {u (R := K)} =
    PrimeSpectrum.zeroLocus (RingHom.ker (bEval (R := K)).toRingHom) := by
  ext p
  constructor
  · intro hp
    have hu : u (R := K) ∈ p.asIdeal := hp (by simp)
    have hv : v (R := K) ∈ p.asIdeal := p.isPrime.mem_of_pow_mem 2 (by
      have hr : v (R := K) ^ 2 = u * v + u ^ 3 := by linear_combination relation (R := K)
      rw [hr]
      exact p.asIdeal.add_mem (p.asIdeal.mul_mem_right v hu)
        (p.asIdeal.pow_mem_of_mem hu 3 (by omega)))
    apply ker_le_of_present bPresent bPresent_surjective bEval p.asIdeal
    · intro i; fin_cases i <;> simp [bEval, u, v]
    · intro i
      fin_cases i
      · simpa using hu
      · simpa using hv
  · intro hp z hz
    rcases hz with rfl
    apply hp
    simp [RingHom.mem_ker, bEval, u]

instance spec_finitePresentation {S : Type u} [CommRing S] [Algebra K S]
    [Algebra.FinitePresentation K S] :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K S))) := by
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  change (algebraMap K S).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  infer_instance

/-- Over a field, the spectrum structure map has the algebraic smooth locus. -/
theorem spec_smooth_iff {S : Type u} [CommRing S] [Algebra K S]
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K S)))]
    (p : PrimeSpectrum S) :
    p ∈ (Spec.map (CommRingCat.ofHom (algebraMap K S))).smoothLocus ↔
      p ∈ Algebra.smoothLocus K S := by
  let q := PrimeSpectrum.comap (algebraMap K S) p
  let e := IsLocalization.atUnits K q.asIdeal.primeCompl
    (S := (Spec.structureSheaf K).presheaf.stalk q) (by
      intro z hz
      exact isUnit_iff_ne_zero.mpr (fun h ↦ hz (h ▸ q.asIdeal.zero_mem)))
  let : IsIso (toStalk K q) := (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
  let T := (structurePresheafInCommRingCat S).stalk p
  let : Algebra K T := ((algebraMap S T).comp (algebraMap K S)).toAlgebra
  let : IsScalarTower K S T := IsScalarTower.of_algebraMap_eq' rfl
  change RingHom.FormallySmooth
    ((Spec.sheafedSpaceMap (CommRingCat.ofHom (algebraMap K S))).hom.stalkMap p).hom ↔
      Algebra.FormallySmooth K (Localization.AtPrime p.asIdeal)
  rw [← RingHom.FormallySmooth.respectsIso.cancel_left_isIso (toStalk K q),
    ← CommRingCat.hom_comp]
  erw [stalkMap_toStalk (CommRingCat.ofHom (algebraMap K S)) p]
  rw [CommRingCat.hom_comp]
  change (algebraMap K T).FormallySmooth ↔ _
  rw [RingHom.formallySmooth_algebraMap]
  exact (Algebra.FormallySmooth.iff_of_equiv ((stalkIso S p).restrictScalars K)).symm

/-- Smooth points cannot lie over a nonsmooth closed origin. -/
theorem smooth_disjoint_origin {S : Type*} [CommRing S] [Algebra K S]
    (e : S →ₐ[K] K) (hn : ¬ Algebra.FormallySmooth K
      (Localization.AtPrime (RingHom.ker e.toRingHom))) :
    Algebra.smoothLocus K S ⊆ (PrimeSpectrum.zeroLocus (RingHom.ker e.toRingHom))ᶜ := by
  intro p hp he
  have hm := RingHom.ker_isMaximal_of_surjective e.toRingHom
    (fun r ↦ ⟨algebraMap K S r, e.commutes r⟩)
  have h := hm.eq_of_le p.isPrime.ne_top he
  have ep : p = (⟨RingHom.ker e.toRingHom, inferInstance⟩ : PrimeSpectrum S) :=
    PrimeSpectrum.ext h.symm
  subst p
  exact hn hp

variable (K)

/-- The two vanishing branch coordinates define the origin image. -/
theorem a_zeroLocus_origin : PrimeSpectrum.zeroLocus {x (R := K), y} =
    Set.range (aOrigin K) := a_zeroLocus.trans (range_aOrigin K).symm

/-- The vanishing conductor defines the one-gon origin image. -/
theorem b_zeroLocus_origin : PrimeSpectrum.zeroLocus {u (R := K)} =
    Set.range (bOrigin K) := b_zeroLocus.trans (range_bOrigin K).symm

/-- The smooth locus of the split node is the complement of its origin. -/
theorem a_smooth_complement : ((aToBase K).smoothLocus : Set (PolygonNodeBranches.node K)) =
    (Set.range (aOrigin K))ᶜ := by
  rw [range_aOrigin]
  apply Set.Subset.antisymm
  · intro p hp
    exact smooth_disjoint_origin (K := K) aEval (a_origin_not_formallySmooth (K := K))
      ((spec_smooth_iff p).mp hp)
  · rw [← a_zeroLocus, ← PolygonNodeBranches.branches_cover_complement]
    exact a_branches_smooth K

/-- The smooth locus of the one-gon chart is the complement of its origin. -/
theorem b_smooth_complement : ((bToBase K).smoothLocus : Set (Spec (.of (B (R := K))))) =
    (Set.range (bOrigin K))ᶜ := by
  rw [range_bOrigin]
  apply Set.Subset.antisymm
  · intro p hp
    exact smooth_disjoint_origin (K := K) bEval (b_origin_not_formallySmooth (K := K))
      ((spec_smooth_iff p).mp hp)
  · rw [← b_zeroLocus, ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, ← range_bPuncture]
    exact b_puncture_smooth K

/-- The algebraic smooth locus of the split node. -/
theorem a_smoothLocus : Algebra.smoothLocus K (A (R := K)) =
    (PrimeSpectrum.zeroLocus (RingHom.ker (aEval (R := K)).toRingHom))ᶜ := by
  rw [← range_aOrigin, ← a_smooth_complement]
  ext p
  exact (spec_smooth_iff p).symm

/-- The algebraic smooth locus of the one-gon chart. -/
theorem b_smoothLocus : Algebra.smoothLocus K (B (R := K)) =
    (PrimeSpectrum.zeroLocus (RingHom.ker (bEval (R := K)).toRingHom))ᶜ := by
  rw [← range_bOrigin, ← b_smooth_complement]
  ext p
  exact (spec_smooth_iff p).symm

end FLT.Mazur.PolygonNodePresentation
