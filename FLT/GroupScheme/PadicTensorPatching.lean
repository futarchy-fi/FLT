/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PadicModulePatching

/-!
# Tensor-compatible arithmetic intersection

A finite projective module over the global coefficient ring is the intersection
of its away and local scalar extensions. Applying this to a tensor product
supplies the intersection assertion needed for descending comultiplication.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace ThreeAdicPlan.PadicPatching

section ScalarExtension

variable {R : Type*} [CommRing R] (S T : Type*) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (N : Type*) [AddCommGroup N] [Module R N]

/-- The map between scalar extensions induced by a map of coefficient rings. -/
def scalarExtensionMap : S ⊗[R] N →ₗ[R] T ⊗[R] N :=
  TensorProduct.map (IsScalarTower.toAlgHom R S T).toLinearMap LinearMap.id

@[simp] theorem scalarExtensionMap_tmul (s : S) (n : N) :
    scalarExtensionMap S T N (s ⊗ₜ[R] n) = algebraMap S T s ⊗ₜ[R] n := rfl

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι R N)

/-- Coordinates on a scalar extension, in a basis of the original module. -/
def scalarExtensionCoordinates : S ⊗[R] N ≃ₗ[S] (ι → S) :=
  by
    classical
    exact (b.equivFun.baseChange R S N (ι → R)).trans
      (TensorProduct.piScalarRight R S S ι)

@[simp] theorem scalarExtensionCoordinates_tmul (s : S) (n : N) (i : ι) :
    scalarExtensionCoordinates S N b (s ⊗ₜ[R] n) i =
      s * algebraMap R S (b.equivFun n i) := by
  simp [scalarExtensionCoordinates, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, Algebra.smul_def, mul_comm]

/-- Coordinates commute with the map between scalar extensions. -/
theorem scalarExtensionCoordinates_map (z : S ⊗[R] N) (i : ι) :
    scalarExtensionCoordinates T N b (scalarExtensionMap S T N z) i =
      algebraMap S T (scalarExtensionCoordinates S N b z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul s n => simp [IsScalarTower.algebraMap_apply R S T]
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- Scalar extension commutes with the tensor square of a module. -/
def tensorScalarExtensionEquiv :
    ((S ⊗[R] N) ⊗[S] (S ⊗[R] N)) ≃ₗ[S] S ⊗[R] (N ⊗[R] N) :=
  (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R S S S N S N).trans
    (TensorProduct.AlgebraTensorModule.congr (TensorProduct.lid S S)
      (LinearEquiv.refl R (N ⊗[R] N)))

@[simp] theorem tensorScalarExtensionEquiv_tmul (s t : S) (x y : N) :
    tensorScalarExtensionEquiv S N ((s ⊗ₜ[R] x) ⊗ₜ[S] (t ⊗ₜ[R] y)) =
      (s * t) ⊗ₜ[R] (x ⊗ₜ[R] y) := by
  simp [tensorScalarExtensionEquiv]

end ScalarExtension

variable (p : ℕ) [Fact p.Prime] (d : ℤ) [Fact (¬ (p : ℤ) ∣ d)]
    (N : Type*) [AddCommGroup N] [Module (Base d) N]
    [Module.Finite (Base d) N] [Module.Projective (Base d) N]

/-- A finite projective global module is exactly the intersection of its away and
local scalar extensions inside the common local generic fibre. -/
theorem scalarExtension_intersection (a : Away d p ⊗[Base d] N) :
    (∃ n : N, (1 : Away d p) ⊗ₜ[Base d] n = a) ↔
    ∃ b : ℤ_[p] ⊗[Base d] N,
      scalarExtensionMap (Away d p) ℚ_[p] N a =
        scalarExtensionMap ℤ_[p] ℚ_[p] N b := by
  classical
  let : NeZero d := ⟨denominator_ne_zero p d⟩
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨1 ⊗ₜ[Base d] n, by simp⟩
  · rintro ⟨z, hz⟩
    let ι := Module.Free.ChooseBasisIndex (Base d) N
    let b := Module.Free.chooseBasis (Base d) N
    let := Fintype.ofFinite ι
    have hc (i : ι) :
        algebraMap (Away d p) ℚ_[p] (scalarExtensionCoordinates (Away d p) N b a i) =
          algebraMap ℤ_[p] ℚ_[p] (scalarExtensionCoordinates ℤ_[p] N b z i) := by
      have h := congrArg (fun t ↦ scalarExtensionCoordinates ℚ_[p] N b t i) hz
      simpa only [scalarExtensionCoordinates_map] using h
    have hr (i : ι) : ∃ r : Base d, algebraMap (Base d) ℚ_[p] r =
        algebraMap (Away d p) ℚ_[p] (scalarExtensionCoordinates (Away d p) N b a i) := by
      apply exists_away_of_padic_integral p d (Base d) (Away d p)
      rw [hc]
      exact PadicInt.norm_le_one _
    choose r hr using hr
    refine ⟨b.equivFun.symm r, ?_⟩
    apply (scalarExtensionCoordinates (Away d p) N b).injective
    ext i
    apply FaithfulSMul.algebraMap_injective (Away d p) ℚ_[p]
    simp only [scalarExtensionCoordinates_tmul, one_mul, LinearEquiv.apply_symm_apply]
    rw [← IsScalarTower.algebraMap_apply (Base d) (Away d p) ℚ_[p]]
    exact hr i

/-- The tensor square of a finite projective module is the intersection of the
away and local tensor squares, in the common local generic tensor square. -/
theorem tensorScalarExtension_intersection
    (a : (Away d p ⊗[Base d] N) ⊗[Away d p] (Away d p ⊗[Base d] N)) :
    (∃ z : N ⊗[Base d] N,
      (tensorScalarExtensionEquiv (Away d p) N).symm (1 ⊗ₜ[Base d] z) = a) ↔
    ∃ b : (ℤ_[p] ⊗[Base d] N) ⊗[ℤ_[p]] (ℤ_[p] ⊗[Base d] N),
      scalarExtensionMap (Away d p) ℚ_[p] (N ⊗[Base d] N)
          (tensorScalarExtensionEquiv (Away d p) N a) =
        scalarExtensionMap ℤ_[p] ℚ_[p] (N ⊗[Base d] N)
          (tensorScalarExtensionEquiv ℤ_[p] N b) := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(tensorScalarExtensionEquiv ℤ_[p] N).symm (1 ⊗ₜ[Base d] z), ?_⟩
    simp
  · rintro ⟨b, hb⟩
    obtain ⟨z, hz⟩ := (scalarExtension_intersection p d (N ⊗[Base d] N)
      (tensorScalarExtensionEquiv (Away d p) N a)).2
        ⟨tensorScalarExtensionEquiv ℤ_[p] N b, hb⟩
    exact ⟨z, (tensorScalarExtensionEquiv (Away d p) N).symm_apply_eq.mpr hz⟩

section Patch

variable {p d} {M : Type*} [AddCommGroup M] [Module (Away d p) M]
    {L : Submodule ℤ_[p] (ℚ_[p] ⊗[Away d p] M)} (P : ModulePatch p d M L)

/-- The common generic fibre of a module patch, via the away comparison. -/
def ModulePatch.genericEquiv :
    ℚ_[p] ⊗[Base d] P.Carrier ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[Away d p] M :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange
    (Base d) (Away d p) ℚ_[p] ℚ_[p] P.Carrier).symm.trans
      (P.awayEquiv.baseChange (Away d p) ℚ_[p] _ _)

@[simp] theorem ModulePatch.genericEquiv_tmul (r : ℚ_[p]) (x : P.Carrier) :
    P.genericEquiv (r ⊗ₜ[Base d] x) = r ⊗ₜ[Away d p] P.awayEquiv (1 ⊗ₜ[Base d] x) := by
  simp [ModulePatch.genericEquiv]

/-- The generic comparison agrees with the away base-change equivalence. -/
theorem ModulePatch.genericEquiv_away (a : Away d p ⊗[Base d] P.Carrier) :
    P.genericEquiv (scalarExtensionMap (Away d p) ℚ_[p] P.Carrier a) =
      1 ⊗ₜ[Away d p] P.awayEquiv a := by
  induction a using TensorProduct.inductionOn with
  | tmul s x =>
    rw [scalarExtensionMap_tmul, ModulePatch.genericEquiv_tmul]
    have h : s ⊗ₜ[Base d] x = s • ((1 : Away d p) ⊗ₜ[Base d] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, TensorProduct.tmul_smul]
    simp only [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  | add a b ha hb => simp [ha, hb, TensorProduct.tmul_add]

/-- The prescribed lattice embedding agrees with the same generic comparison.
This is the compatibility field of a patch extended to every local section. -/
theorem ModulePatch.genericEquiv_local (a : ℤ_[p] ⊗[Base d] P.Carrier) :
    P.genericEquiv (scalarExtensionMap ℤ_[p] ℚ_[p] P.Carrier a) =
      (P.localEquiv a).val := by
  induction a using TensorProduct.inductionOn with
  | tmul s x =>
    rw [scalarExtensionMap_tmul, ModulePatch.genericEquiv_tmul]
    have h : s ⊗ₜ[Base d] x = s • ((1 : ℤ_[p]) ⊗ₜ[Base d] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    change (algebraMap ℤ_[p] ℚ_[p] s) ⊗ₜ[Away d p] P.awayEquiv (1 ⊗ₜ[Base d] x) =
      s • (P.localEquiv (1 ⊗ₜ[Base d] x)).val
    rw [← P.compatible]
    simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb

/-- Every module patch realizes the actual intersection in the specified generic
fibre, not merely an abstract isomorphic module. -/
theorem ModulePatch.intersection (a : M) :
    (∃ x : P.Carrier, P.awayEquiv (1 ⊗ₜ[Base d] x) = a) ↔
      (1 : ℚ_[p]) ⊗ₜ[Away d p] a ∈ L := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [P.compatible]
    exact (P.localEquiv (1 ⊗ₜ[Base d] x)).property
  · intro ha
    let b := P.localEquiv.symm ⟨1 ⊗ₜ[Away d p] a, ha⟩
    have h : scalarExtensionMap (Away d p) ℚ_[p] P.Carrier (P.awayEquiv.symm a) =
        scalarExtensionMap ℤ_[p] ℚ_[p] P.Carrier b := by
      apply P.genericEquiv.injective
      rw [P.genericEquiv_away, P.genericEquiv_local, P.awayEquiv.apply_symm_apply]
      simp [b]
    obtain ⟨x, hx⟩ := (scalarExtension_intersection p d P.Carrier
      (P.awayEquiv.symm a)).2 ⟨b, h⟩
    exact ⟨x, P.awayEquiv.eq_symm_apply.mp hx⟩

/-- Away base change of the patched tensor square. -/
def ModulePatch.tensorAwayEquiv :
    Away d p ⊗[Base d] (P.Carrier ⊗[Base d] P.Carrier) ≃ₗ[Away d p]
      M ⊗[Away d p] M :=
  (tensorScalarExtensionEquiv (Away d p) P.Carrier).symm.trans
    (TensorProduct.congr P.awayEquiv P.awayEquiv)

/-- Local base change of the patched tensor square. -/
def ModulePatch.tensorLocalEquiv :
    ℤ_[p] ⊗[Base d] (P.Carrier ⊗[Base d] P.Carrier) ≃ₗ[ℤ_[p]] L ⊗[ℤ_[p]] L :=
  (tensorScalarExtensionEquiv ℤ_[p] P.Carrier).symm.trans
    (TensorProduct.congr P.localEquiv P.localEquiv)

/-- The patched tensor square is exactly the intersection of the prescribed away
and local tensor squares. The equality is tested in their common generic fibre,
with each input transported by its base-change equivalence. -/
theorem ModulePatch.tensor_intersection (a : M ⊗[Away d p] M) :
    (∃ z : P.Carrier ⊗[Base d] P.Carrier,
      P.tensorAwayEquiv (1 ⊗ₜ[Base d] z) = a) ↔
    ∃ b : L ⊗[ℤ_[p]] L,
      scalarExtensionMap (Away d p) ℚ_[p] (P.Carrier ⊗[Base d] P.Carrier)
          (P.tensorAwayEquiv.symm a) =
        scalarExtensionMap ℤ_[p] ℚ_[p] (P.Carrier ⊗[Base d] P.Carrier)
          (P.tensorLocalEquiv.symm b) := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨P.tensorLocalEquiv (1 ⊗ₜ[Base d] z), ?_⟩
    simp
  · rintro ⟨b, hb⟩
    obtain ⟨z, hz⟩ := (scalarExtension_intersection p d (P.Carrier ⊗[Base d] P.Carrier)
      (P.tensorAwayEquiv.symm a)).2 ⟨P.tensorLocalEquiv.symm b, hb⟩
    exact ⟨z, P.tensorAwayEquiv.eq_symm_apply.mp hz⟩


/-- The tensor of the common generic-fibre equivalence. -/
def ModulePatch.genericTensorEquiv :
    ℚ_[p] ⊗[Base d] (P.Carrier ⊗[Base d] P.Carrier) ≃ₗ[ℚ_[p]]
      (ℚ_[p] ⊗[Away d p] M) ⊗[ℚ_[p]] (ℚ_[p] ⊗[Away d p] M) :=
  (tensorScalarExtensionEquiv ℚ_[p] P.Carrier).symm.trans
    (TensorProduct.congr P.genericEquiv P.genericEquiv)

/-- The prescribed local tensor square maps to the common generic tensor square
by tensoring the given inclusion of the lattice. -/
def latticeTensorMap : L ⊗[ℤ_[p]] L →ₗ[ℤ_[p]]
    (ℚ_[p] ⊗[Away d p] M) ⊗[ℚ_[p]] (ℚ_[p] ⊗[Away d p] M) :=
  (TensorProduct.lift ((TensorProduct.mk ℚ_[p] _ _).restrictScalars₁₂ ℤ_[p] ℤ_[p])).comp
    (TensorProduct.map L.subtype L.subtype)

@[simp] theorem latticeTensorMap_tmul (x y : L) :
    latticeTensorMap (L := L) (x ⊗ₜ[ℤ_[p]] y) = x.val ⊗ₜ[ℚ_[p]] y.val := rfl

/-- The away tensor square maps to the common generic tensor square by extension
of scalars. -/
def awayTensorMap : M ⊗[Away d p] M →ₗ[Away d p]
    (ℚ_[p] ⊗[Away d p] M) ⊗[ℚ_[p]] (ℚ_[p] ⊗[Away d p] M) :=
  ((tensorScalarExtensionEquiv ℚ_[p] M).symm.toLinearMap.restrictScalars (Away d p)).comp
    (TensorProduct.mk (Away d p) ℚ_[p] (M ⊗[Away d p] M) 1)

@[simp] theorem awayTensorMap_tmul (x y : M) :
    awayTensorMap (p := p) (d := d) (x ⊗ₜ[Away d p] y) =
      ((1 : ℚ_[p]) ⊗ₜ[Away d p] x) ⊗ₜ[ℚ_[p]] ((1 : ℚ_[p]) ⊗ₜ[Away d p] y) := by
  simp [awayTensorMap, tensorScalarExtensionEquiv]

/-- The tensor comparison commutes with the away generic-fibre map. -/
theorem ModulePatch.genericTensorEquiv_away
    (a : Away d p ⊗[Base d] (P.Carrier ⊗[Base d] P.Carrier)) :
    P.genericTensorEquiv (scalarExtensionMap (Away d p) ℚ_[p] _ a) =
      awayTensorMap (p := p) (d := d) (P.tensorAwayEquiv a) := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb
  | tmul s z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy
    | tmul x y =>
      simp only [scalarExtensionMap_tmul]
      suffices
          ((1 : ℚ_[p]) ⊗ₜ[Away d p] P.awayEquiv (1 ⊗ₜ[Base d] x)) ⊗ₜ[ℚ_[p]]
            (algebraMap (Away d p) ℚ_[p] s ⊗ₜ[Away d p] P.awayEquiv (1 ⊗ₜ[Base d] y)) =
          ((1 : ℚ_[p]) ⊗ₜ[Away d p] P.awayEquiv (1 ⊗ₜ[Base d] x)) ⊗ₜ[ℚ_[p]]
            ((1 : ℚ_[p]) ⊗ₜ[Away d p] P.awayEquiv (s ⊗ₜ[Base d] y)) by
        simpa [ModulePatch.genericTensorEquiv, ModulePatch.tensorAwayEquiv,
          tensorScalarExtensionEquiv, awayTensorMap] using this
      rw [← P.genericEquiv_away (s ⊗ₜ[Base d] y),
        scalarExtensionMap_tmul, ModulePatch.genericEquiv_tmul]

/-- The tensor comparison uses the prescribed lattice inclusion on local sections. -/
theorem ModulePatch.genericTensorEquiv_local
    (a : ℤ_[p] ⊗[Base d] (P.Carrier ⊗[Base d] P.Carrier)) :
    P.genericTensorEquiv (scalarExtensionMap ℤ_[p] ℚ_[p] _ a) =
      latticeTensorMap (L := L) (P.tensorLocalEquiv a) := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb
  | tmul s z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy
    | tmul x y =>
      suffices
          ((1 : ℚ_[p]) ⊗ₜ[Away d p] P.awayEquiv (1 ⊗ₜ[Base d] x)) ⊗ₜ[ℚ_[p]]
            (algebraMap ℤ_[p] ℚ_[p] s ⊗ₜ[Away d p] P.awayEquiv (1 ⊗ₜ[Base d] y)) =
          (P.localEquiv (1 ⊗ₜ[Base d] x)).val ⊗ₜ[ℚ_[p]]
            (P.localEquiv (s ⊗ₜ[Base d] y)).val by
        simpa [ModulePatch.genericTensorEquiv, ModulePatch.tensorLocalEquiv,
          tensorScalarExtensionEquiv] using this
      rw [← P.genericEquiv_local (1 ⊗ₜ[Base d] x),
        ← P.genericEquiv_local (s ⊗ₜ[Base d] y)]
      simp

/-- The tensor square of the patch is the intersection in the original common
generic fibre: the away map and the local map here use the specified module and
lattice, rather than coordinates on the constructed patch. -/
theorem ModulePatch.tensor_intersection_native (a : M ⊗[Away d p] M) :
    (∃ z : P.Carrier ⊗[Base d] P.Carrier, P.tensorAwayEquiv (1 ⊗ₜ[Base d] z) = a) ↔
    ∃ b : L ⊗[ℤ_[p]] L, awayTensorMap (p := p) (d := d) a = latticeTensorMap b := by
  rw [P.tensor_intersection]
  apply exists_congr
  intro b
  rw [← P.genericTensorEquiv.injective.eq_iff,
    P.genericTensorEquiv_away, P.genericTensorEquiv_local,
    P.tensorAwayEquiv.apply_symm_apply, P.tensorLocalEquiv.apply_symm_apply]

end Patch

end ThreeAdicPlan.PadicPatching
