/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.RepresentationTheory.Irreducible
public import FLT.Slop.RepresentationTheory.OddAbsIrredSlop
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Burnside spanning for absolutely irreducible representations

This file packages the linear-algebra input used in de Smit--Lenstra's trace-descent argument.
-/

@[expose] public section

open scoped MonoidAlgebra TensorProduct

universe u

namespace Representation

noncomputable section

variable {k G V : Type u} [Field k] [Group G] [AddCommGroup V] [Module k V]

private lemma exists_smul_eq_of_irreducible_isAlgClosed [FiniteDimensional k V]
    [IsAlgClosed k] (rho : Representation k G V) (hirr : rho.IsIrreducible)
    (T : Module.End k V) (hT : ∀ g : G, Commute (rho g) T) :
    ∃ μ : k, T = μ • (1 : Module.End k V) := by
  let _ : IsSimpleModule k[G] rho.asModule :=
    (irreducible_iff_isSimpleModule_asModule rho).mp hirr
  let f : rho.IntertwiningMap rho :=
    { toLinearMap := T
      isIntertwining' := fun g => by
        simpa [Module.End.mul_eq_comp] using (hT g).eq.symm }
  let f' : Module.End k[G] rho.asModule :=
    IntertwiningMap.equivLinearMapAsModule rho rho f
  obtain ⟨μ, hμ⟩ :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2 f'
  refine ⟨μ, LinearMap.ext fun v => ?_⟩
  have hμv := LinearMap.congr_fun hμ v
  change μ • v = T v at hμv
  exact hμv.symm

/-- Over an algebraically closed field, an irreducible representation spans its full
endomorphism algebra. -/
lemma adjoinRange_eq_top_of_isAlgClosed [FiniteDimensional k V] [IsAlgClosed k]
    (rho : Representation k G V) (hirr : rho.IsIrreducible) :
    Slop.OddRep.adjoinRange rho = ⊤ :=
  Slop.OddRep.adjoinRange_eq_top rho hirr
    (exists_smul_eq_of_irreducible_isAlgClosed rho hirr)

private lemma nontrivial_of_isAbsolutelyIrreducible
    (rho : Representation k G V) [habs : IsAbsolutelyIrreducible.{u} rho] : Nontrivial V := by
  have hirrBase : (k ⊗ᵣ' rho).IsIrreducible :=
    IsAbsolutelyIrreducible.absolutelyIrreducible (ρ := rho) (self := habs)
      k inferInstance inferInstance
  have hirr : rho.IsIrreducible :=
    Slop.OddRep.isIrreducible_of_baseChange rho k hirrBase
  let _ : IsSimpleModule k[G] rho.asModule :=
    (irreducible_iff_isSimpleModule_asModule rho).mp hirr
  exact IsSimpleModule.nontrivial k[G] rho.asModule

private lemma exists_smul_eq_of_isAbsolutelyIrreducible
    {n : Type} [Finite n]
    (rho : Representation k G (n → k)) [habs : IsAbsolutelyIrreducible.{u} rho]
    (T : Module.End k (n → k)) (hT : ∀ g : G, Commute (rho g) T) :
    ∃ μ : k, T = μ • (1 : Module.End k (n → k)) := by
  let L := AlgebraicClosure k
  let rhoL : Representation L G (L ⊗[k] (n → k)) := L ⊗ᵣ' rho
  let TL : Module.End L (L ⊗[k] (n → k)) := T.baseChange L
  have hirrL : rhoL.IsIrreducible :=
    IsAbsolutelyIrreducible.absolutelyIrreducible (ρ := rho) (self := habs)
      L inferInstance inferInstance
  have hTL : ∀ g : G, Commute (rhoL g) TL := by
    intro g
    exact (hT g).map (Module.End.baseChangeHom k L (n → k))
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_irreducible_isAlgClosed rhoL hirrL TL hTL
  let _ : Nontrivial (n → k) := nontrivial_of_isAbsolutelyIrreducible rho
  have hn : Nonempty n := by
    classical
    rcases isEmpty_or_nonempty n with hn | hn
    · let _ := hn
      exact (not_subsingleton (n → k) inferInstance).elim
    · exact hn
  classical
  let _ := Fintype.ofFinite n
  let i₀ : n := hn.some
  let e₀ : n → k := Pi.single i₀ 1
  let μ : k := T e₀ i₀
  have hcμ : c = algebraMap k L μ := by
    have h := LinearMap.congr_fun hc (1 ⊗ₜ[k] e₀)
    have h' := congrArg (fun x : L ⊗[k] (n → k) ↦
      TensorProduct.piScalarRight k L L n x i₀) h
    simpa [TL, e₀, μ, Pi.single_apply, Algebra.smul_def] using h'.symm
  refine ⟨μ, LinearMap.ext fun v ↦ funext fun i ↦ ?_⟩
  have h := LinearMap.congr_fun hc (1 ⊗ₜ[k] v)
  have h' := congrArg (fun x : L ⊗[k] (n → k) ↦
    TensorProduct.piScalarRight k L L n x i) h
  rw [hcμ] at h'
  apply (algebraMap k L).injective
  simpa [TL, μ, Algebra.smul_def, mul_comm] using h'

/-- Burnside's theorem in the form used for framed deformations: an absolutely irreducible
representation on a coordinate space generates the full endomorphism algebra. -/
lemma adjoinRange_eq_top_of_isAbsolutelyIrreducible
    {n : Type} [Finite n]
    (rho : Representation k G (n → k)) [habs : IsAbsolutelyIrreducible.{u} rho] :
    Slop.OddRep.adjoinRange rho = ⊤ :=
  have hirrBase : (k ⊗ᵣ' rho).IsIrreducible :=
    IsAbsolutelyIrreducible.absolutelyIrreducible (ρ := rho) (self := habs)
      k inferInstance inferInstance
  have hirr : rho.IsIrreducible :=
    Slop.OddRep.isIrreducible_of_baseChange rho k hirrBase
  Slop.OddRep.adjoinRange_eq_top rho hirr
    (exists_smul_eq_of_isAbsolutelyIrreducible rho)

/-- Matrix of a representation on a coordinate vector space. -/
def representationMatrix {A H : Type u} {n : Type} [CommSemiring A] [Monoid H]
    [Fintype n] [DecidableEq n]
    (rho : Representation A H (n → A)) (g : H) : Matrix n n A :=
  LinearMap.toMatrixAlgEquiv' (rho g)

private lemma span_range_eq_adjoinRange (rho : Representation k G V) :
    Submodule.span k (Set.range rho) =
      (Slop.OddRep.adjoinRange rho).toSubmodule := by
  symm
  apply Algebra.adjoin_eq_span_of_subset
  rw [MonoidHom.mclosure_range rho, MonoidHom.coe_mrange]
  exact Submodule.subset_span

/-- The matrices of an absolutely irreducible representation span the full matrix algebra. -/
lemma span_range_representationMatrix_eq_top
    {n : Type} [Fintype n] [DecidableEq n]
    (rho : Representation k G (n → k)) [habs : IsAbsolutelyIrreducible.{u} rho] :
    Submodule.span k (Set.range (representationMatrix rho)) = ⊤ := by
  let e : Module.End k (n → k) ≃ₗ[k] Matrix n n k :=
    LinearMap.toMatrixAlgEquiv'.toLinearEquiv
  have hspan : Submodule.span k (Set.range rho) = ⊤ := by
    rw [span_range_eq_adjoinRange, adjoinRange_eq_top_of_isAbsolutelyIrreducible rho]
    rfl
  have hmap := congrArg (Submodule.map e.toLinearMap) hspan
  have himage : e '' Set.range rho = Set.range (representationMatrix rho) := by
    ext M
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨rho g, ⟨g, rfl⟩, rfl⟩
  simpa [Submodule.map_span, himage] using hmap

/-- An absolutely irreducible representation admits a finite matrix basis drawn from its image. -/
lemma exists_basis_representationMatrix
    {n : Type} [Fintype n] [DecidableEq n]
    (rho : Representation k G (n → k)) [IsAbsolutelyIrreducible.{u} rho] :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι → G)
      (b : Module.Basis ι k (Matrix n n k)),
      ∀ i, b i = representationMatrix rho (g i) := by
  let s : Set (Matrix n n k) := Set.range (representationMatrix rho)
  have hs : ⊤ ≤ Submodule.span k s := by
    rw [span_range_representationMatrix_eq_top rho]
  let b := Module.Basis.ofSpan hs
  let _ : Fintype ((linearIndepOn_empty k id).extend (Set.empty_subset s)) :=
    Fintype.ofFinite _
  let g : (linearIndepOn_empty k id).extend (Set.empty_subset s) → G := fun i ↦
    (Module.Basis.ofSpan_subset hs (Set.mem_range_self i)).choose
  refine ⟨_, inferInstance, g, b, fun i ↦ ?_⟩
  calc
    b i = (i : Matrix n n k) := Module.Basis.ofSpan_apply_self hs i
    _ = representationMatrix rho (g i) := by
      simpa [g] using
        (Module.Basis.ofSpan_subset hs (Set.mem_range_self i)).choose_spec.symm

/-- The trace pairing `(A, B) ↦ Tr(AB)` on a full matrix algebra. -/
def matrixTracePairing {A : Type u} {n : Type} [CommRing A] [Fintype n] :
    LinearMap.BilinForm A (Matrix n n A) :=
  LinearMap.compr₂ (LinearMap.mul A (Matrix n n A)) (Matrix.traceLinearMap n A A)

@[simp]
lemma matrixTracePairing_apply {A : Type u} {n : Type} [CommRing A] [Fintype n]
    (X Y : Matrix n n A) : matrixTracePairing X Y = (X * Y).trace := rfl

/-- The trace pairing on a full matrix algebra is nondegenerate. -/
lemma matrixTracePairing_nondegenerate {n : Type} [Fintype n] :
    (matrixTracePairing (A := k) (n := n)).Nondegenerate := by
  constructor
  · intro A hA
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro B
    simpa using hA B
  · intro B hB
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro A
    simpa using hB A

/-- In any basis of the full matrix algebra, the Gram matrix of the trace pairing is invertible. -/
lemma det_matrixTracePairing_ne_zero
    {n : Type} {ι : Type u} [Fintype n] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k (Matrix n n k)) :
    ((matrixTracePairing (A := k) (n := n)).toMatrix b).det ≠ 0 :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    matrixTracePairing_nondegenerate

/-- The form of Burnside's theorem used in trace descent: there is a finite family of group
elements whose matrices form a basis and whose trace-pairing matrix is invertible. -/
lemma exists_tracePairing_basis
    {n : Type} [Fintype n] [DecidableEq n]
    (rho : Representation k G (n → k)) [IsAbsolutelyIrreducible.{u} rho] :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (g : ι → G)
      (b : Module.Basis ι k (Matrix n n k)),
      (∀ i, b i = representationMatrix rho (g i)) ∧
        Matrix.det ((fun i j ↦
          (representationMatrix rho (g i * g j)).trace) : Matrix ι ι k) ≠ 0 := by
  classical
  obtain ⟨ι, hι, g, b, hb⟩ := exists_basis_representationMatrix rho
  let _ : Fintype ι := hι
  let _ : DecidableEq ι := Classical.decEq ι
  refine ⟨ι, inferInstance, inferInstance, g, b, hb, ?_⟩
  have hmatrix :
      (matrixTracePairing (A := k) (n := n)).toMatrix b =
        ((fun i j ↦ (representationMatrix rho (g i * g j)).trace) : Matrix ι ι k) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, matrixTracePairing_apply, hb i, hb j]
    simp [representationMatrix]
  rw [← hmatrix]
  exact det_matrixTracePairing_ne_zero b

end

end Representation
