/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PadicPatchingArithmetic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Intersections with a finite p-adic lattice

The intersection construction is expressed in coordinates on the module away from `p`.
The local lattice is arbitrary: its basis need not have rational coordinates.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable (p : ℕ) [Fact p.Prime]

/-- A finitely generated `ℤ_p`-submodule of a finite coordinate space has bounded
 denominators, uniformly on all its elements. -/
theorem padic_lattice_bounded {ι : Type*} [Finite ι]
    (L : Submodule ℤ_[p] (ι → ℚ_[p])) (hL : L.FG) :
    ∃ n : ℕ, ∀ x ∈ L, ∀ i, ‖(p : ℚ_[p]) ^ n * x i‖ ≤ 1 := by
  let := padic_isLocalization_away p
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hL
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (p : ℤ_[p])) (fun j : Fin m × ι ↦ g j.1 j.2)
  refine ⟨n, ?_⟩
  intro x hx
  rw [← hg] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    intro i
    obtain ⟨a, ha⟩ := hn (j, i)
    have he : (a : ℚ_[p]) = (p : ℚ_[p]) ^ n * g j i := by
      simpa [Algebra.smul_def] using ha
    rw [← he]
    exact a.property
  | zero => simp
  | add x y hx hy ihx ihy =>
    intro i
    simpa only [Pi.add_apply, mul_add] using
      (Padic.nonarchimedean ((p : ℚ_[p]) ^ n * x i)
        ((p : ℚ_[p]) ^ n * y i)).trans (max_le (ihx i) (ihy i))
  | smul a x hx ih =>
    intro i
    change ‖(p : ℚ_[p]) ^ n * ((a : ℚ_[p]) * x i)‖ ≤ 1
    rw [mul_left_comm, norm_mul]
    exact (mul_le_mul_of_nonneg_right a.property (norm_nonneg _)).trans
      (by simpa using ih i)

/-- Clearing powers of `p` in the span of a local lattice. -/
theorem padic_exists_pow_smul_mem {ι : Type*}
    (L : Submodule ℤ_[p] (ι → ℚ_[p])) {x : ι → ℚ_[p]}
    (hx : x ∈ Submodule.span ℚ_[p] (L : Set (ι → ℚ_[p]))) :
    ∃ n : ℕ, (p : ℤ_[p]) ^ n • x ∈ L := by
  let := padic_isLocalization_away p
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    convert L.add_mem (L.smul_mem ((p : ℤ_[p]) ^ m) hn)
      (L.smul_mem ((p : ℤ_[p]) ^ n) hm) using 1
    simp only [smul_add, smul_smul, pow_add, mul_comm]
  | smul a x hx ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (p : ℤ_[p]) a
    refine ⟨n + m, ?_⟩
    convert L.smul_mem b hm using 1
    ext i
    change (p : ℚ_[p]) ^ (n + m) * (a * x i) =
      (b : ℚ_[p]) * ((p : ℚ_[p]) ^ m * x i)
    have hb' : a * (p : ℚ_[p]) ^ n = b := by simpa using hb
    rw [← hb', pow_add]
    ring

/-- Increasing the power used to clear denominators preserves lattice membership. -/
theorem padic_pow_smul_mem_mono {ι : Type*}
    (L : Submodule ℤ_[p] (ι → ℚ_[p])) {x : ι → ℚ_[p]} {n m : ℕ}
    (hn : (p : ℤ_[p]) ^ n • x ∈ L) (hnm : n ≤ m) :
    (p : ℤ_[p]) ^ m • x ∈ L := by
  simpa only [smul_smul, ← pow_add, Nat.sub_add_cancel hnm] using
    L.smul_mem ((p : ℤ_[p]) ^ (m - n)) hn

/-- A full local lattice contains a power of `p` times the standard lattice. -/
theorem padic_lattice_contains_standard {ι : Type*} [Finite ι]
    (L : Submodule ℤ_[p] (ι → ℚ_[p]))
    (hspan : Submodule.span ℚ_[p] (L : Set (ι → ℚ_[p])) = ⊤) :
    ∃ k : ℕ, ∀ v : ι → ℤ_[p], (fun i ↦ (p : ℚ_[p]) ^ k * v i) ∈ L := by
  classical
  let := Fintype.ofFinite ι
  have hi (i : ι) : ∃ n : ℕ, (p : ℤ_[p]) ^ n • (Pi.single i 1 : ι → ℚ_[p]) ∈ L :=
    padic_exists_pow_smul_mem p L (by rw [hspan]; trivial)
  choose n hn using hi
  let k := Finset.univ.sup n
  have hk (i : ι) : (p : ℤ_[p]) ^ k • (Pi.single i 1 : ι → ℚ_[p]) ∈ L :=
    padic_pow_smul_mem_mono p L (hn i) (Finset.le_sup (Finset.mem_univ i))
  refine ⟨k, fun v ↦ ?_⟩
  convert L.sum_mem (fun i (_ : i ∈ Finset.univ) ↦ L.smul_mem (v i) (hk i)) using 1
  ext i
  simp [Pi.single_apply, mul_comm, Algebra.smul_def]

section Intersection

variable (R S : Type*) [CommRing R] [CommRing S]
  [Algebra R S] [Algebra R ℚ_[p]] [Algebra S ℚ_[p]] [IsScalarTower R S ℚ_[p]]
  [Algebra R ℤ_[p]] [IsScalarTower R ℤ_[p] ℚ_[p]]
  {ι : Type*}

/-- The coordinatewise embedding into the local vector space. -/
def padicCoordinateMap : (ι → S) →ₗ[R] (ι → ℚ_[p]) :=
  LinearMap.pi fun i ↦ (IsScalarTower.toAlgHom R S ℚ_[p]).toLinearMap.comp
    (LinearMap.proj i)

omit [Algebra R ℤ_[p]] [IsScalarTower R ℤ_[p] ℚ_[p]] in
@[simp]
theorem padicCoordinateMap_apply (x : ι → S) (i : ι) :
    padicCoordinateMap p R S x i = algebraMap S ℚ_[p] (x i) := rfl

/-- The global intersection module: sections away from `p` whose local images lie
in the prescribed `p`-adic lattice. -/
def padicIntersection (L : Submodule ℤ_[p] (ι → ℚ_[p])) : Submodule R (ι → S) :=
  (L.restrictScalars R).comap (padicCoordinateMap p R S)

@[simp]
theorem mem_padicIntersection (L : Submodule ℤ_[p] (ι → ℚ_[p])) (x : ι → S) :
    x ∈ padicIntersection p R S L ↔ padicCoordinateMap p R S x ∈ L := Iff.rfl

/-- The intersection maps into the prescribed local lattice. -/
def padicIntersectionToLocal (L : Submodule ℤ_[p] (ι → ℚ_[p])) :
    padicIntersection p R S L →ₗ[R] L :=
  ((padicCoordinateMap p R S).comp (padicIntersection p R S L).subtype).codRestrict
    (L.restrictScalars R) (fun x ↦ x.property)

@[simp]
theorem padicIntersectionToLocal_apply (L : Submodule ℤ_[p] (ι → ℚ_[p]))
    (x : padicIntersection p R S L) (i : ι) :
    (padicIntersectionToLocal p R S L x).val i = algebraMap S ℚ_[p] (x.val i) := rfl

/-- The intersection of a finite `p`-adic lattice with a free module over
`ℤ[1/(dp)]` is finite over `ℤ[1/d]`. -/
theorem padicIntersection_finite [Finite ι] [IsNoetherianRing R]
    [FaithfulSMul S ℚ_[p]] [Algebra ℤ R] [Algebra ℤ S]
    (d : ℤ) [IsLocalization.Away d R] [IsLocalization.Away (d * p) S]
    (L : Submodule ℤ_[p] (ι → ℚ_[p])) (hL : L.FG) :
    Module.Finite R (padicIntersection p R S L) := by
  classical
  obtain ⟨n, hn⟩ := padic_lattice_bounded p L hL
  let q : (ι → R) →ₗ[R] (ι → ℚ_[p]) := padicCoordinateMap p R R
  let f : padicIntersection p R S L →ₗ[R] (ι → ℚ_[p]) :=
    (p : R) ^ n • ((padicCoordinateMap p R S).comp (padicIntersection p R S L).subtype)
  have hf : ∀ x, f x ∈ q.range := by
    intro x
    have hx := hn _ x.property
    have hi (i : ι) : ‖algebraMap S ℚ_[p] ((p : S) ^ n * x.val i)‖ ≤ 1 := by
      simpa using hx i
    choose r hr using fun i ↦ exists_away_of_padic_integral p d R S _ (hi i)
    refine ⟨r, ?_⟩
    ext i
    simpa [q, f, padicCoordinateMap, Algebra.smul_def] using hr i
  let f' : padicIntersection p R S L →ₗ[R] q.range := f.codRestrict q.range hf
  have hinj : Function.Injective f' := by
    intro x y hxy
    apply Subtype.ext
    funext i
    apply FaithfulSMul.algebraMap_injective S ℚ_[p]
    have he := congrArg (fun z : q.range ↦ z.val i) hxy
    have hp : (p : ℚ_[p]) ^ n ≠ 0 := pow_ne_zero _ (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)
    apply mul_left_cancel₀ hp
    simpa [f', f, padicCoordinateMap, Algebra.smul_def] using he
  exact Module.Finite.of_injective f' hinj

/-- Over a principal ideal domain the intersection lattice is projective. -/
theorem padicIntersection_projective [Finite ι] [IsDomain R] [IsPrincipalIdealRing R]
    [Module.IsTorsionFree R S] [FaithfulSMul S ℚ_[p]] [Algebra ℤ R] [Algebra ℤ S]
    (d : ℤ) [IsLocalization.Away d R] [IsLocalization.Away (d * p) S]
    (L : Submodule ℤ_[p] (ι → ℚ_[p])) (hL : L.FG) :
    Module.Projective R (padicIntersection p R S L) := by
  let := padicIntersection_finite p R S d L hL
  infer_instance

/-- Inverting `p` recovers the original module from its intersection lattice. -/
theorem padicIntersection_isLocalizedModule [IsLocalization.Away (p : R) S]
    (L : Submodule ℤ_[p] (ι → ℚ_[p]))
    (hspan : Submodule.span ℚ_[p] (L : Set (ι → ℚ_[p])) = ⊤) :
    IsLocalizedModule (Submonoid.powers (p : R)) (padicIntersection p R S L).subtype := by
  apply IsLocalizedModule.mk
  · intro s
    rw [← (Algebra.lsmul R (A := S) R (ι → S)).commutes]
    exact (IsLocalization.map_units S s).map _
  · intro x
    obtain ⟨n, hn⟩ := padic_exists_pow_smul_mem p L
      (show padicCoordinateMap p R S x ∈ Submodule.span ℚ_[p] (L : Set _) by
        rw [hspan]; trivial)
    have hm : (p : R) ^ n • x ∈ padicIntersection p R S L := by
      change padicCoordinateMap p R S ((p : R) ^ n • x) ∈ L
      convert hn using 1
      ext i
      simp [padicCoordinateMap, Algebra.smul_def]
    exact ⟨(⟨(p : R) ^ n • x, hm⟩, ⟨(p : R) ^ n, n, rfl⟩), rfl⟩
  · intro x y hxy
    exact ⟨1, by simpa using Subtype.ext hxy⟩

/-- The canonical base-change isomorphism away from `p`. -/
def padicIntersectionAwayEquiv [IsLocalization.Away (p : R) S]
    (L : Submodule ℤ_[p] (ι → ℚ_[p]))
    (hspan : Submodule.span ℚ_[p] (L : Set (ι → ℚ_[p])) = ⊤) :
    S ⊗[R] padicIntersection p R S L ≃ₗ[S] (ι → S) := by
  let := padicIntersection_isLocalizedModule p R S L hspan
  exact (IsLocalizedModule.isBaseChange (Submonoid.powers (p : R)) S
    (padicIntersection p R S L).subtype).equiv

/-- On pure tensors, the localization comparison is the expected scalar multiplication. -/
theorem padicIntersectionAwayEquiv_tmul [IsLocalization.Away (p : R) S]
    (L : Submodule ℤ_[p] (ι → ℚ_[p]))
    (hspan : Submodule.span ℚ_[p] (L : Set (ι → ℚ_[p])) = ⊤)
    (s : S) (x : padicIntersection p R S L) :
    padicIntersectionAwayEquiv p R S L hspan (s ⊗ₜ[R] x) = s • x.val := by
  exact IsBaseChange.equiv_tmul _ _ _

/-- Every element of the local lattice is generated over `ℤ_p` by elements of
 the global intersection. -/
theorem padicIntersection_local_surjective [Finite ι]
    [Algebra ℤ S] (d : ℤ) [IsLocalization.Away (d * p) S]
    (L : Submodule ℤ_[p] (ι → ℚ_[p]))
    (hspan : Submodule.span ℚ_[p] (L : Set (ι → ℚ_[p])) = ⊤) :
    Function.Surjective ((padicIntersectionToLocal p R S L).liftBaseChange ℤ_[p]) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨k, hk⟩ := padic_lattice_contains_standard p L hspan
  intro x
  choose s o he using fun i ↦ exists_away_add_padic p d S (x.val i) k
  have hs : s ∈ padicIntersection p R S L := by
    change padicCoordinateMap p R S s ∈ L
    convert L.sub_mem x.property (hk o) using 1
    ext i
    exact (eq_sub_iff_add_eq.mpr (he i).symm)
  have hg (i : ι) : Pi.single i ((p : S) ^ k) ∈ padicIntersection p R S L := by
    change padicCoordinateMap p R S _ ∈ L
    convert hk (Pi.single i 1) using 1
    ext j
    by_cases h : j = i <;> simp [padicCoordinateMap, h]
  let g (i : ι) : padicIntersection p R S L := ⟨Pi.single i ((p : S) ^ k), hg i⟩
  refine ⟨1 ⊗ₜ[R] (⟨s, hs⟩ : padicIntersection p R S L) +
    ∑ i, o i ⊗ₜ[R] g i, ?_⟩
  simp only [map_add, map_sum, LinearMap.liftBaseChange_tmul, one_smul]
  apply Subtype.ext
  ext i
  simpa [g, Pi.single_apply, Algebra.smul_def, apply_ite, mul_comm] using (he i).symm

/-- Flatness of the intersection makes its local base-change map injective. -/
theorem padicIntersection_local_injective [Finite ι] [IsLocalization.Away (p : R) S]
    (L : Submodule ℤ_[p] (ι → ℚ_[p]))
    (hspan : Submodule.span ℚ_[p] (L : Set (ι → ℚ_[p])) = ⊤)
    [Module.Flat R (padicIntersection p R S L)] :
    Function.Injective ((padicIntersectionToLocal p R S L).liftBaseChange ℤ_[p]) := by
  let := padicIntersection_isLocalizedModule p R S L hspan
  have hS := IsLocalizedModule.isBaseChange (Submonoid.powers (p : R)) S
    (padicIntersection p R S L).subtype
  have hpi : IsBaseChange ℚ_[p] (padicCoordinateMap p S S (ι := ι)) :=
    IsBaseChange.pi (fun _ ↦ Algebra.linearMap S ℚ_[p])
      (fun _ ↦ IsBaseChange.linearMap S ℚ_[p])
  have hK := hS.comp hpi
  let j : ℤ_[p] →ₗ[R] ℚ_[p] := (IsScalarTower.toAlgHom R ℤ_[p] ℚ_[p]).toLinearMap
  let g := j.rTensor (padicIntersection p R S L)
  have hg : Function.Injective g :=
    Module.Flat.rTensor_preserves_injective_linearMap j Subtype.val_injective
  have hc : (hK.equiv.toLinearMap.restrictScalars R).comp g =
      (L.subtype.restrictScalars R).comp
        (((padicIntersectionToLocal p R S L).liftBaseChange ℤ_[p]).restrictScalars R) := by
    ext o x i
    change hK.equiv (j o ⊗ₜ[R] x) i =
      ((padicIntersectionToLocal p R S L).liftBaseChange ℤ_[p] (o ⊗ₜ[R] x)).val i
    rw [IsBaseChange.equiv_tmul, LinearMap.liftBaseChange_tmul]
    rfl
  intro a b hab
  apply hg
  apply hK.equiv.injective
  have ha := LinearMap.congr_fun hc a
  have hb := LinearMap.congr_fun hc b
  exact ha.trans ((congrArg Subtype.val hab).trans hb.symm)

/-- Patching recovers the prescribed local lattice after base change to `ℤ_p`. -/
def padicIntersectionLocalEquiv [Finite ι] [IsLocalization.Away (p : R) S]
    [Algebra ℤ S] (d : ℤ) [IsLocalization.Away (d * p) S]
    (L : Submodule ℤ_[p] (ι → ℚ_[p]))
    (hspan : Submodule.span ℚ_[p] (L : Set (ι → ℚ_[p])) = ⊤)
    [Module.Flat R (padicIntersection p R S L)] :
    ℤ_[p] ⊗[R] padicIntersection p R S L ≃ₗ[ℤ_[p]] L :=
  LinearEquiv.ofBijective ((padicIntersectionToLocal p R S L).liftBaseChange ℤ_[p])
    ⟨padicIntersection_local_injective p R S L hspan,
      padicIntersection_local_surjective p R S d L hspan⟩

/-- The local comparison sends a pure tensor to scalar multiplication of its image. -/
theorem padicIntersectionLocalEquiv_tmul [Finite ι] [IsLocalization.Away (p : R) S]
    [Algebra ℤ S] (d : ℤ) [IsLocalization.Away (d * p) S]
    (L : Submodule ℤ_[p] (ι → ℚ_[p]))
    (hspan : Submodule.span ℚ_[p] (L : Set (ι → ℚ_[p])) = ⊤)
    [Module.Flat R (padicIntersection p R S L)]
    (o : ℤ_[p]) (x : padicIntersection p R S L) :
    padicIntersectionLocalEquiv p R S d L hspan (o ⊗ₜ[R] x) =
      o • padicIntersectionToLocal p R S L x := by
  exact LinearMap.liftBaseChange_tmul _ _ _ _

end Intersection

end ThreeAdicPlan
