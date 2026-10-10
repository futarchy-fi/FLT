/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedLaurentTerminalMap
public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentSmooth

/-!
# The equality-depth component introduces no extra identifications

The complete conic and Laurent maps are injective and have exactly their
original incidence intersection. Consequently the glued map is injective,
and its Laurent chart is the entire pullback of the original terminal chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => WeierstrassCurve.a₁ (W.map (residue R))
local notation "c" => residue R (Data.b6 d)
local notation "C₀" => ConicCoordinate a c
local notation "B" => MiddleConicOpen (W.map (residue R)) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "X" => finiteGlobalTensorModel hπ data K (j + 1) hj

local notation "C" => laurentTerminalOriginalConic hπ data D j hj hk
variable (hp : 2 * (start + j + 1) = depth)
local notation "ψ" => residueLaurentConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "G" => terminalLaurentChart hπ data D (j + 1) hj
  (Nat.zero_lt_succ (start + j)) hk hp
local notation "P" => laurentConicComponent D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "l" => laurentConicComponentConic D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "r" => laurentConicComponentTorus D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

local notation "f" => laurentTerminalComponentMap hπ data D j hj hk hp

/-- The complete original conic map identifies no distinct points. -/
theorem laurentTerminalOriginalConic_injective : Function.Injective C := by
  by_cases h : 0 < start + j
  · rw [laurentTerminalOriginalConic_positive hπ data D j hj hk h]
    exact (g).isOpenEmbedding.injective.comp
      (residueSuccessiveConicImmersion D (start + j) h hk
        (Data.b3 d) (Data.b4 d) (Data.b6 d)
        (Data.factor3 d) (Data.factor4 d)).isClosedEmbedding.injective
  · rw [laurentTerminalOriginalConic_zero hπ data D j hj hk (by omega)]
    exact (g).isOpenEmbedding.injective.comp
      (zeroResidueConicImmersion D (start + j) (by omega) hk
        (Data.b3 d) (Data.b4 d) (Data.b6 d)
        (Data.factor3 d) (Data.factor4 d)).isClosedEmbedding.injective

/-- Opposite chart points coincide only through the original conic incidence open. -/
theorem laurentTerminalComponent_cross {x : Spec (.of C₀)}
    {y : Spec (.of (K[T;T⁻¹]))} (h : C x = G y) : l x = r y := by
  obtain ⟨z, hz, hx⟩ := Scheme.exists_preimage_of_isPullback
    (laurentTerminalOriginalConic_isPullback hπ data D j hj hk hp) y x h.symm
  rw [← hx, ← hz]
  exact congrArg (fun m => m z) (laurentConicComponent_condition D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp)

/-- Gluing the actual two complete charts introduces no additional point identifications. -/
theorem laurentTerminalComponentMap_injective : Function.Injective f := by
  intro x y hxy
  rcases laurentConicComponent_cover D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
    (Data.factor6 d) hp x with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;>
    rcases laurentConicComponent_cover D (start + j) hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
      (Data.factor6 d) hp y with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · simp only [← Scheme.Hom.comp_apply, laurentTerminalComponentMap_conic] at hxy
    exact congrArg l (laurentTerminalOriginalConic_injective hπ data D j hj hk hxy)
  · simp only [← Scheme.Hom.comp_apply, laurentTerminalComponentMap_conic,
      laurentTerminalComponentMap_torus] at hxy
    exact laurentTerminalComponent_cross hπ data D j hj hk hp hxy
  · simp only [← Scheme.Hom.comp_apply, laurentTerminalComponentMap_conic,
      laurentTerminalComponentMap_torus] at hxy
    exact (laurentTerminalComponent_cross hπ data D j hj hk hp hxy.symm).symm
  · simp only [← Scheme.Hom.comp_apply, laurentTerminalComponentMap_torus] at hxy
    exact congrArg r ((G).isOpenEmbedding.injective hxy)

/-- The whole inverse image of the original Laurent chart is precisely the glued torus. -/
theorem laurentTerminalComponentMap_torus_preimage : f ⁻¹' Set.range G = Set.range r := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, laurentTerminalComponentMap_injective hπ data D j hj hk hp ?_⟩
    exact (congrArg (fun m => m y)
      (laurentTerminalComponentMap_torus hπ data D j hj hk hp)).trans hy
  · rintro ⟨y, rfl⟩
    exact ⟨y, congrArg (fun m => m y)
      (laurentTerminalComponentMap_torus hπ data D j hj hk hp).symm⟩

/-- The Laurent chart square is cartesian in the actual finite model. -/
theorem laurentTerminalComponentMap_torus_isPullback : IsPullback (𝟙 _) r G f := by
  apply IsOpenImmersion.isPullback
  · rw [Category.id_comp, laurentTerminalComponentMap_torus]
  · exact TopologicalSpace.Opens.ext
      (laurentTerminalComponentMap_torus_preimage hπ data D j hj hk hp)

end FLT.Mazur.WeierstrassDividedDepth
