/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.QuotientCurve

/-!
# Vélu coefficient sums

The sums run over every nonzero kernel point, so no choice of representatives modulo negation
is needed. In characteristic different from two, the summands are half the usual paired
summands: `t = ∑ (6x² + b₂x + b₄)/2` and
`w = ∑ (10x³ + 2b₂x² + 3b₄x + b₆)/2`.

The resulting Weierstrass equation is defined here without asserting its nonsingularity.
-/

@[expose] public section

noncomputable section

open scoped BigOperators WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

variable {K : Type*} [Field K]

/-- The affine x-coordinate, extended by zero at the identity for use in finite sums. -/
def xCoord {E : WeierstrassCurve K} : E.toAffine.Point → K
  | .zero => 0
  | .some x _ _ => x

/-- The affine y-coordinate, extended by zero at the identity for use in finite sums. -/
def yCoord {E : WeierstrassCurve K} : E.toAffine.Point → K
  | .zero => 0
  | .some _ y _ => y

/-- Half of the paired contribution to Vélu's coefficient `t`. -/
def tTerm (E : WeierstrassCurve K) (x : K) : K :=
  (6 * x ^ 2 + E.b₂ * x + E.b₄) / 2

/-- Half of the paired contribution to Vélu's coefficient `w`. -/
def wTerm (E : WeierstrassCurve K) (x : K) : K :=
  (10 * x ^ 3 + 2 * E.b₂ * x ^ 2 + 3 * E.b₄ * x + E.b₆) / 2

section Coefficients

variable [DecidableEq K] (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point)

/-- The nonzero points of the subgroup used in Vélu's sums. -/
abbrev Nonzero := {P : G // (P : E.toAffine.Point) ≠ 0}

/-- Vélu's coefficient `t`, summed over all nonzero points of the kernel. -/
def t [Fintype G] : K := by
  classical
  exact ∑ P : Nonzero E G, tTerm E (xCoord P.val.val)

/-- Vélu's coefficient `w`, summed over all nonzero points of the kernel. -/
def w [Fintype G] : K := by
  classical
  exact ∑ P : Nonzero E G, wTerm E (xCoord P.val.val)

/-- The candidate Vélu equation. Its ellipticity requires a separate theorem about the kernel. -/
def curve [Fintype G] : WeierstrassCurve K where
  a₁ := E.a₁
  a₂ := E.a₂
  a₃ := E.a₃
  a₄ := E.a₄ - 5 * t E G
  a₆ := E.a₆ - E.b₂ * t E G - 7 * w E G

end Coefficients

section Descent

variable {L : Type*} [Field L] [DecidableEq L] [Algebra K L]
variable (E₀ : WeierstrassCurve K)

/-- The extended x-coordinate commutes with the Galois action. -/
theorem xCoord_map (σ : L ≃ₐ[K] L) (P : (E₀⁄L).Point) :
    xCoord (Affine.Point.map (W' := E₀) σ.toAlgHom P) = σ (xCoord P) := by
  cases P <;> simp [xCoord, Affine.Point.map]

/-- The extended y-coordinate commutes with the Galois action. -/
theorem yCoord_map (σ : L ≃ₐ[K] L) (P : (E₀⁄L).Point) :
    yCoord (Affine.Point.map (W' := E₀) σ.toAlgHom P) = σ (yCoord P) := by
  cases P <;> simp [yCoord, Affine.Point.map]

omit [DecidableEq L] in
/-- The `t` summand is equivariant under automorphisms of the coefficient field. -/
theorem tTerm_map (σ : L ≃ₐ[K] L) (x : L) :
    σ (tTerm (E₀⁄L) x) =
      tTerm (E₀⁄L) (σ x) := by
  simp [tTerm, Affine.baseChange, baseChange, map_ofNat]

omit [DecidableEq L] in
/-- The `w` summand is equivariant under automorphisms of the coefficient field. -/
theorem wTerm_map (σ : L ≃ₐ[K] L) (x : L) :
    σ (wTerm (E₀⁄L) x) =
      wTerm (E₀⁄L) (σ x) := by
  simp [wTerm, Affine.baseChange, baseChange, map_ofNat]

variable (H : AddSubgroup (E₀⁄L).Point)

/-- Galois stability restricts an automorphism to a permutation of the nonzero kernel points. -/
def nonzeroEquiv (σ : L ≃ₐ[K] L)
    (hH : ∀ (τ : L ≃ₐ[K] L) P, P ∈ H → Affine.Point.map (W' := E₀) τ.toAlgHom P ∈ H) :
    Nonzero (E₀⁄L) H ≃ Nonzero (E₀⁄L) H where
  toFun P := ⟨⟨Affine.Point.map (W' := E₀) σ.toAlgHom P.val.val, hH σ _ P.val.property⟩,
    fun h ↦ P.property ((Affine.Point.map_injective σ.toAlgHom)
      (h.trans (map_zero _).symm))⟩
  invFun P := ⟨⟨Affine.Point.map (W' := E₀) σ.symm.toAlgHom P.val.val,
    hH σ.symm _ P.val.property⟩,
    fun h ↦ P.property ((Affine.Point.map_injective σ.symm.toAlgHom)
      (h.trans (map_zero _).symm))⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    rcases P with ⟨⟨P, _⟩, _⟩
    cases P <;> simp only [Affine.Point.map, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
    all_goals rfl
  right_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    rcases P with ⟨⟨P, _⟩, _⟩
    cases P <;> simp only [Affine.Point.map, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    all_goals rfl

/-- Vélu's coefficient `t` is fixed when the finite kernel is Galois stable. -/
theorem t_fixed [Fintype H]
    (hH : ∀ (τ : L ≃ₐ[K] L) P, P ∈ H → Affine.Point.map (W' := E₀) τ.toAlgHom P ∈ H)
    (σ : L ≃ₐ[K] L) : σ (t (E₀⁄L) H) =
      t (E₀⁄L) H := by
  classical
  apply galois_fixed_sum_of_equiv σ (nonzeroEquiv E₀ H σ hH)
  intro P
  exact (tTerm_map E₀ σ _).trans
    (congrArg (tTerm _) (xCoord_map E₀ σ P.val.val).symm)

/-- Vélu's coefficient `w` is fixed when the finite kernel is Galois stable. -/
theorem w_fixed [Fintype H]
    (hH : ∀ (τ : L ≃ₐ[K] L) P, P ∈ H → Affine.Point.map (W' := E₀) τ.toAlgHom P ∈ H)
    (σ : L ≃ₐ[K] L) : σ (w (E₀⁄L) H) =
      w (E₀⁄L) H := by
  classical
  apply galois_fixed_sum_of_equiv σ (nonzeroEquiv E₀ H σ hH)
  intro P
  exact (wTerm_map E₀ σ _).trans
    (congrArg (wTerm _) (xCoord_map E₀ σ P.val.val).symm)

/-- The candidate Vélu equation of a Galois-stable finite subgroup descends to the base field.
This constructs the equation only, with no nonsingularity assertion. -/
theorem exists_curve [IsGalois K L] [Fintype H]
    (hH : ∀ (τ : L ≃ₐ[K] L) P, P ∈ H → Affine.Point.map (W' := E₀) τ.toAlgHom P ∈ H) :
    ∃ E' : WeierstrassCurve K,
      E'.map (algebraMap K L) = curve (E₀⁄L) H := by
  obtain ⟨t₀, ht⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    (t_fixed E₀ H hH)
  obtain ⟨w₀, hw⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    (w_fixed E₀ H hH)
  refine ⟨⟨E₀.a₁, E₀.a₂, E₀.a₃, E₀.a₄ - 5 * t₀, E₀.a₆ - E₀.b₂ * t₀ - 7 * w₀⟩, ?_⟩
  simp [curve, Affine.baseChange, baseChange, WeierstrassCurve.map, ht, hw, b₂, map_ofNat]

end Descent

end WeierstrassCurve.Velu
