/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicCover

/-!
# Scheme descent on the complete conic incidence open

The two original Laurent punctures form an actual open cover, at every
preceding depth including zero. They therefore detect equality of maps
to arbitrary schemes, rather than only equality on points.
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

/-- The two original ordered Laurent punctures, indexed without changing parameters. -/
def residueConicPuncture (i : Fin 2) :
    Spec (.of K[T;T⁻¹]) ⟶ Spec (.of (MiddleConicOpen W₀ c)) :=
  if i = 0 then s₁ else s₂

include hk b3 b4 h3 h4 in
/-- Each original puncture is an open subscheme of the full incidence boundary. -/
theorem residueConicPuncture_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (residueConicPuncture D k b6 h6 hp i) := by
  have H : IsOpenImmersion (residueConicPuncture D k b6 h6 hp i ≫ s) := by
    fin_cases i
    · change IsOpenImmersion (s₁ ≫ s)
      rw [residueNodeConicFirst_spec]
      change IsOpenImmersion ((I).hom ≫ PolygonNodeBranches.right K)
      infer_instance
    · change IsOpenImmersion (s₂ ≫ s)
      rw [residueNodeConicSecond_spec]
      change IsOpenImmersion ((I).hom ≫ PolygonNodeBranches.left K)
      infer_instance
  exact IsOpenImmersion.of_comp _ s

/-- The full original incidence boundary is covered by its two ordered Laurent punctures. -/
def residueConicPunctureOpenCover : (Spec (.of (MiddleConicOpen W₀ c))).OpenCover where
  I₀ := Fin 2
  X := fun _ => Spec (.of K[T;T⁻¹])
  f := residueConicPuncture D k b6 h6 hp
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, residueConicPuncture_isOpenImmersion D k hk b3 b4 b6 h3 h4 h6 hp⟩
    intro z
    have H : z ∈ Set.range s₁ ∪ Set.range s₂ := by
      rw [residueNodeConicPunctures_cover D k hk b3 b4 b6 h3 h4 h6 hp]
      trivial
    rcases H with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨0, t, ht⟩
    · exact ⟨1, t, ht⟩

include hk b3 b4 h3 h4 in
/-- Equality on the two whole punctures proves equality of boundary scheme morphisms. -/
theorem residueConicPunctures_hom_ext {Y : Scheme.{u}}
    (f g : Spec (.of (MiddleConicOpen W₀ c)) ⟶ Y)
    (h₁ : s₁ ≫ f = s₁ ≫ g) (h₂ : s₂ ≫ f = s₂ ≫ g) : f = g := by
  apply (residueConicPunctureOpenCover D k hk b3 b4 b6 h3 h4 h6 hp).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · exact h₁
  · exact h₂

end FLT.Mazur.WeierstrassSuccessiveX
