/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueConicBoundaryGeometry
public import FLT.Mazur.WeierstrassDividedResidueMiddleIntersection

/-!
# The entire divided chart intersects the original conic exactly in its boundary

Pasting the actual residue overlap with the original conic boundary square
identifies the complete fiber product, before terminal normalization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "t" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "m" => WeierstrassSuccessiveX.residueMiddleTransition D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "hk'" => Nat.zero_lt_succ (start + j)

open WeierstrassSuccessiveX WeierstrassModificationX
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 d)
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "C" => residueSuccessiveConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)

local notation "f" => globalDividedTensorChart hπ data K (j + 1) hj

/-- The original conic boundary map into the whole divided chart. -/
def conicToDivided := (E).hom ≫
  Spec.map (CommRingCat.ofHom (AlgEquiv.toRingEquiv m).toRingHom) ≫
    PrincipalOpenTensor.inclusion K x

/-- The whole divided chart and the whole conic have exactly the original boundary. -/
theorem globalDividedConic_isPullback :
    IsPullback (conicToDivided data D j hj hk0 hk) i f (C ≫ g) := by
  have H := residueConicBoundary_isPullback D (start + j) hk0 hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
  exact H.paste_horiz (globalResidue_middleOverlap_isPullback hπ data D j hj hk0 hk)

/-- The full intersection comparison uses the established conic incidence open. -/
def globalDividedConicPullbackIso : Spec (.of B) ≅ pullback f (C ≫ g) :=
  (globalDividedConic_isPullback hπ data D j hj hk0 hk).isoPullback

/-- The intersection comparison retains the entire divided-chart projection. -/
@[reassoc] theorem globalDividedConicPullbackIso_divided :
    (globalDividedConicPullbackIso hπ data D j hj hk0 hk).hom ≫
      pullback.fst f (C ≫ g) = conicToDivided data D j hj hk0 hk :=
  (globalDividedConic_isPullback hπ data D j hj hk0 hk).isoPullback_hom_fst

/-- The intersection comparison retains the original inclusion into the conic. -/
@[reassoc] theorem globalDividedConicPullbackIso_conic :
    (globalDividedConicPullbackIso hπ data D j hj hk0 hk).hom ≫
      pullback.snd f (C ≫ g) = i :=
  (globalDividedConic_isPullback hπ data D j hj hk0 hk).isoPullback_hom_snd

/-- No conic point outside the original boundary lies in the divided chart. -/
theorem globalDividedConic_preimage : (C ≫ g) ⁻¹' Set.range f = Set.range i := by
  have H := globalDividedConic_isPullback hπ data D j hj hk0 hk
  ext z
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨p, _, hp⟩ := Scheme.exists_preimage_of_isPullback H w z hw
    exact ⟨p, hp⟩
  · rintro ⟨p, rfl⟩
    exact ⟨conicToDivided data D j hj hk0 hk p,
      congrArg (fun morphism => morphism p) H.w⟩

end FLT.Mazur.WeierstrassDividedDepth
