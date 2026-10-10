/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicBranches
public import FLT.Mazur.PrincipalOpenNormalization
public import FLT.Mazur.WeierstrassDividedTerminalConicCover

/-!
# The entire terminal conic boundary at every preceding depth

Normalize the original divided localization directly. This includes depth zero
and preserves both original ordered punctures and their reciprocal coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) < n)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K
local notation "e" => WeierstrassDilatation.residuePolygonEquiv D (k + 1)
  (Nat.zero_lt_succ k) hk b3 b4 b6 h3 h4 h6 hp
local notation "Q" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso (AlgEquiv.toRingEquiv
    (residueDividedConicOpenEquiv D k hk b3 b4 b6 h3 h4))))
local notation "E" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso (AlgEquiv.toRingEquiv e)))
local notation "b" => Spec.map (CommRingCat.ofHom
  (algebraMap (PolygonNodeEqualizer.A (R := K)) (Localization.Away ((e) tx))))
local notation "ψ" => residueNodeConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (k + 1) hp b6 h6)
local notation "s₁" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))
local notation "I" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (LaurentPolynomial.invert (R := K)))))

/-- The original oriented map is the full normalized principal inclusion at every depth. -/
theorem residueNodeConicMap_spec_boundary :
    s = ((Q) ≪≫ (PrincipalOpenNormalization.specIso e tx).symm).hom ≫ b := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, ← PrincipalOpenNormalization.specIso_inclusion]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact congrArg (fun z => residueDividedConicMap D k hk b3 b4 b6 h3 h4 z)
    ((e).symm_apply_apply z)

/-- The oriented conic boundary is an open subscheme of the terminal node. -/
instance residueNodeConicMap_isOpenImmersion : IsOpenImmersion s := by
  rw [residueNodeConicMap_spec_boundary]
  infer_instance

/-- The full conic boundary is exactly the union of the two punctured node branches. -/
theorem residueNodeConicMap_range :
    Set.range s = Set.range (PolygonNodeBranches.left K) ∪
      Set.range (PolygonNodeBranches.right K) := by
  rw [residueNodeConicMap_spec_boundary]
  rw [WeierstrassDividedDepth.conicBoundary_range_iso_comp]
  have hx := WeierstrassDilatation.residuePolygonEquiv_x D (k + 1)
    (Nat.zero_lt_succ k) hk b3 b4 b6 h3 h4 h6 hp
  exact (WeierstrassDividedDepth.conicBoundary_range_away _).trans
    ((congrArg (fun z : PolygonNodeEqualizer.A (R := K) =>
      (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum (PolygonNodeEqualizer.A (R := K))))) hx).trans
       (PolygonNodeBranches.branches_cover_difference
        (WeierstrassDilatation.residueTangentUnit D)⁻¹).symm)

/-- The first ordered puncture has the whole right branch as its normalized image. -/
theorem residueNodeConicFirst_range : Set.range (s₁ ≫ s) =
    Set.range (PolygonNodeBranches.right K) := by
  rw [residueNodeConicFirst_spec]
  change Set.range (fun z => PolygonNodeBranches.right K ((I).hom z)) = _
  exact (I).hom.homeomorph.surjective.range_comp _

/-- The second ordered puncture has the whole left branch as its normalized image. -/
theorem residueNodeConicSecond_range : Set.range (s₂ ≫ s) =
    Set.range (PolygonNodeBranches.left K) := by
  rw [residueNodeConicSecond_spec]
  change Set.range (fun z => PolygonNodeBranches.left K ((I).hom z)) = _
  exact (I).hom.homeomorph.surjective.range_comp _

include hk b3 b4 h3 h4 in
/-- The two actual conic punctures cover every point of the original incidence open. -/
theorem residueNodeConicPunctures_cover : Set.range s₁ ∪ Set.range s₂ = Set.univ := by
  let _ : IsOpenImmersion s := by
    rw [residueNodeConicMap_spec_boundary D k hk b3 b4 b6 h3 h4 h6 hp]
    infer_instance
  ext z
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  have hz : s z ∈ Set.range (PolygonNodeBranches.left K) ∪
      Set.range (PolygonNodeBranches.right K) := by
    rw [← residueNodeConicMap_range D k hk b3 b4 b6 h3 h4 h6 hp]
    exact ⟨z, rfl⟩
  rcases hz with hz | hz
  · rw [← residueNodeConicSecond_range D k hk b3 b4 b6 h3 h4 h6 hp] at hz
    obtain ⟨p, hp⟩ := hz
    exact Or.inr ⟨p, (s).isOpenEmbedding.injective hp⟩
  · rw [← residueNodeConicFirst_range D k hk b3 b4 b6 h3 h4 h6 hp] at hz
    obtain ⟨p, hp⟩ := hz
    exact Or.inl ⟨p, (s).isOpenEmbedding.injective hp⟩

include hk b3 b4 h3 h4 in
/-- The two original punctures share no point, before or after their terminal identification. -/
theorem residueNodeConicPunctures_disjoint : Disjoint (Set.range s₁) (Set.range s₂) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨p, rfl⟩ ⟨q, hq⟩
  have h₁ : s (s₁ p) ∈ Set.range (PolygonNodeBranches.right K) := by
    rw [← residueNodeConicFirst_range D k hk b3 b4 b6 h3 h4 h6 hp]
    exact ⟨p, rfl⟩
  have h₂ : s (s₁ p) ∈ Set.range (PolygonNodeBranches.left K) := by
    rw [← residueNodeConicSecond_range D k hk b3 b4 b6 h3 h4 h6 hp]
    exact ⟨q, congrArg s hq⟩
  exact Set.disjoint_left.mp (PolygonNodeBranches.disjoint_ranges K) h₂ h₁

end FLT.Mazur.WeierstrassSuccessiveX
