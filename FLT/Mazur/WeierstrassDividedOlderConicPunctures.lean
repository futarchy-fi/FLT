/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalConicBoundary
public import FLT.Mazur.WeierstrassDividedTerminalConicCover

/-!
# Ordered punctured conic parameters in every retained stage

The original two conic parameters still give the whole incidence boundary
after all later modifications. Their images are disjoint, and the maps
retain the same parameter functions and tangent ordering.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "g" => olderGlobalTensorChart hπ data K j hj r hr
open WeierstrassModificationX
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "C" => olderGlobalMiddleConic hπ data D j hj r hr hk0 hk
local notation "W₀" => W.map (residue R)
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

variable (hp : 2 * (start + j + 1) < depth)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp (Data.b6 e) (Data.factor6 e))
local notation "f₁" => conicBoundaryFirst W₀ c ha hc
local notation "f₂" => conicBoundarySecond W₀ c ha hc
local notation "s₁" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₁))
local notation "s₂" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₂))
local notation "p₀" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc)))
local notation "b" => olderGlobalConicBoundary hπ data D j hj r hr hk0 hk

/-- The first full retained parameter still restricts to the original first puncture. -/
theorem olderGlobalConicFirst_puncture :
    p₀ ≫ olderGlobalMiddleConicFirstParameter hπ data D j hj r hr hk0 hk = s₁ ≫ b := by
  have H : s₁ ≫ i =
      Spec.map (CommRingCat.ofHom (conicPuncturedFirst W₀ c hc).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact conicBoundaryFirst_base W₀ c ha hc
  calc _ = Spec.map (CommRingCat.ofHom (conicPuncturedFirst W₀ c hc).toRingHom) ≫ C := by
        rw [conicPuncturedFirst_spec c hc W₀ ha]
        simp only [olderGlobalMiddleConicFirstParameter, Category.assoc, WeierstrassCurve.map_a₁]
    _ = _ := by rw [← H, Category.assoc]; rfl

/-- The second full retained parameter keeps the opposite puncture with the same sign. -/
theorem olderGlobalConicSecond_puncture :
    p₀ ≫ olderGlobalMiddleConicSecondParameter hπ data D j hj r hr hk0 hk = s₂ ≫ b := by
  have H : s₂ ≫ i =
      Spec.map (CommRingCat.ofHom (conicPuncturedSecond W₀ c hc).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact conicBoundarySecond_base W₀ c ha hc
  calc _ = Spec.map (CommRingCat.ofHom (conicPuncturedSecond W₀ c hc).toRingHom) ≫ C := by
        rw [conicPuncturedSecond_spec c hc W₀ ha]
        simp only [olderGlobalMiddleConicSecondParameter, Category.assoc, WeierstrassCurve.map_a₁]
    _ = _ := by rw [← H, Category.assoc]; rfl

/-- At every retained stage the two punctured parameters cover the entire original boundary. -/
theorem olderGlobalConicPunctures_cover :
    Set.range (s₁ ≫ b) ∪ Set.range (s₂ ≫ b) = Set.range b := by
  ext z
  constructor
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨s₁ p, rfl⟩
    · exact ⟨s₂ p, rfl⟩
  · rintro ⟨p, rfl⟩
    have H : p ∈ Set.range s₁ ∪ Set.range s₂ := by
      rw [terminalConicPunctures_cover hπ data D j hj hk0 hk hp]
      trivial
    rcases H with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact Or.inl ⟨q, rfl⟩
    · exact Or.inr ⟨q, rfl⟩

/-- Later retention never identifies the two punctured conic components. -/
theorem olderGlobalConicPunctures_disjoint :
    Disjoint (Set.range (s₁ ≫ b)) (Set.range (s₂ ≫ b)) := by
  have H : Function.Injective b := by
    rw [← olderGlobalConicBoundary_transition hπ data D j hj r hr hk0 hk]
    exact ((E).hom ≫ PrincipalOpenTensor.inclusion K t ≫ g).isOpenEmbedding.injective
  apply Set.disjoint_left.mpr
  rintro z ⟨p, rfl⟩ ⟨q, hq⟩
  exact Set.disjoint_left.mp (terminalConicPunctures_disjoint data D j hj hk hp)
    ⟨p, rfl⟩ ⟨q, H hq⟩

end FLT.Mazur.WeierstrassDividedDepth
