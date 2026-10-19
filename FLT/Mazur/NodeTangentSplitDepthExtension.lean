/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentShearRealization
public import FLT.Mazur.FiniteExtensionValuationSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.FieldTheory.Perfect

/-!
# Constructing the split-depth extension of a nonsplit normalized node

The quadratic tangent field, its actual DVR, the local base map, and the
integral shear are constructed together. The extension retains the original
uniformizer, exact depth, valuation restriction and perfect residue field.
-/

@[expose] public noncomputable section
open WeierstrassCurve IsLocalRing
namespace FLT.Mazur

/-- Construct a quadratic split-depth model from the normalized coefficient bounds. -/
theorem exists_nodeTangent_splitDepth_extension {K : Type} [Field K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
    (W : WeierstrassCurve A)
    (hirr : Irreducible ((nodeTangentPolynomial W).map (residue A)))
    {π : A} {n : ℕ} (hn : 0 < n) (hπ0 : π ≠ 0)
    (hπ : maximalIdeal A = Ideal.span {π}) (hb : IsUnit W.b₂)
    (h3 : W.a₃ ∈ maximalIdeal A ^ (n + 1))
    (h4 : W.a₄ ∈ maximalIdeal A ^ (n + 1))
    (h6 : W.a₆ ∈ maximalIdeal A ^ n) (h6' : W.a₆ ∉ maximalIdeal A ^ (n + 1)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L) (B : ValuationSubring L)
      (_ : IsDiscreteValuationRing B) (_ : PerfectField (ResidueField B))
      (φ : A →+* B) (s : B), IsLocalHom φ ∧
      (∀ a : A, (φ a : L) = algebraMap K L a) ∧ B.comap (algebraMap K L) = A ∧
      Module.finrank K L = 2 ∧
      SplitNodeDepth ((VariableChange.mk 1 0 s 0 : VariableChange B) • W.map φ) (φ π) n := by
  obtain ⟨dom, dvr, loc, unram, L, field, algK, fin, sep, algA, towerK,
      algS, towerS, frac, rank, _⟩ := exists_node_tangent_fraction_field K W hirr hb π hπ
  let _ := dom
  let _ := dvr
  let _ := loc
  let _ := field
  let _ := algK
  let _ := fin
  let _ := sep
  let _ := algA
  let _ := towerK
  let _ := algS
  let _ := towerS
  let _ := frac
  let S := AdjoinRoot (nodeTangentPolynomial W)
  let _ : Module.Finite A S := (nodeTangentPolynomial_monic W).finite_adjoinRoot
  let _ : Module.Finite A (ResidueField S) := Module.Finite.trans S (ResidueField S)
  let _ : PerfectField (ResidueField S) := Algebra.IsAlgebraic.perfectField (ResidueField A)
  let B := nodeTangentValuationSubring A W L
  let _ : IsDiscreteValuationRing B := fractionValuationSubring_isDiscreteValuationRing S L
  let _ : PerfectField (ResidueField B) :=
    PerfectField.of_ringEquiv (ResidueField.mapEquiv (nodeTangentValuationEquiv A W L))
  let φ := nodeTangentValuationBaseMap A W L
  have hφ (a : A) : (φ a : L) = algebraMap K L a :=
    (fractionValuationBaseMap_coe (R := S) (K := L) a).trans
      (IsScalarTower.algebraMap_apply A K L a)
  refine ⟨L, field, algK, fin, sep, B, inferInstance, inferInstance, φ,
    nodeTangentValuationRoot A W L, inferInstance, hφ,
    FiniteExtensionValuationSubring.comap_eq A B (algebraMap K L) φ hφ, rank, ?_⟩
  have hd := nodeTangentValuationShear_splitNodeDepth A W L hirr hn hπ0 hπ hb h3 h4 h6 h6'
  rw [nodeTangentValuationShear_eq_rootShear] at hd
  exact hd

end FLT.Mazur
