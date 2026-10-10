/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentComponent
public import FLT.Mazur.WeierstrassDividedTerminalConicCoordinates
public import FLT.Mazur.WeierstrassDividedTerminalZeroConicIntersection

/-!
# The glued equality-depth component in the original finite model

Both complete charts map into the original model through the original atlas.
Their exact intersection, including scale one, proves compatibility. The
resulting map retains all original conic and Laurent points.
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

/-- The entire original terminal conic, with the actual scale-one or positive chart map. -/
def laurentTerminalOriginalConic : Spec (.of C₀) ⟶ X :=
  if h : 0 < start + j then
    residueSuccessiveConicImmersion D (start + j) h hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) ≫ g
  else
    zeroResidueConicImmersion D (start + j) (by omega) hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) ≫ g
local notation "C" => laurentTerminalOriginalConic hπ data D j hj hk

/-- Positive scale retains the complete middle conic immersion. -/
theorem laurentTerminalOriginalConic_positive (h : 0 < start + j) :
    C = residueSuccessiveConicImmersion D (start + j) h hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) ≫ g := by
  simp only [laurentTerminalOriginalConic, dite_eq_left h]

/-- Scale one retains the complete initial conic immersion. -/
theorem laurentTerminalOriginalConic_zero (h : start + j = 0) :
    C = zeroResidueConicImmersion D (start + j) h hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) ≫ g := by
  simp only [laurentTerminalOriginalConic, dite_eq_right (show ¬0 < start + j by omega)]

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

/-- The original incidence open is the entire conic and Laurent intersection at every scale. -/
theorem laurentTerminalOriginalConic_isPullback : IsPullback s i G C := by
  by_cases h : 0 < start + j
  · rw [laurentTerminalOriginalConic_positive hπ data D j hj hk h]
    exact terminalLaurentConicCoordinates_isPullback hπ data D j hj h hk hp
  · rw [laurentTerminalOriginalConic_zero hπ data D j hj hk (by omega)]
    exact terminalLaurentZeroConicCoordinates_isPullback hπ data D j hj (by omega) hk hp

/-- The entire glued component maps to the original finite residue model. -/
def laurentTerminalComponentMap : P ⟶ X :=
  pushout.desc C G (laurentTerminalOriginalConic_isPullback hπ data D j hj hk hp).w.symm
local notation "f" => laurentTerminalComponentMap hπ data D j hj hk hp

/-- The global component map recovers the entire original conic immersion. -/
@[reassoc] theorem laurentTerminalComponentMap_conic : l ≫ f = C := pushout.inl_desc _ _ _

/-- The global component map recovers the complete terminal chart, with its original coordinate. -/
@[reassoc] theorem laurentTerminalComponentMap_torus : r ≫ f = G := pushout.inr_desc _ _ _

/-- The image consists of the full original conic and the full terminal Laurent chart. -/
theorem laurentTerminalComponentMap_range : Set.range f = Set.range C ∪ Set.range G := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases laurentConicComponent_cover D (start + j) hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
      (Data.factor6 d) hp x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, congrArg (fun m => m y)
        (laurentTerminalComponentMap_conic hπ data D j hj hk hp).symm⟩
    · exact Or.inr ⟨y, congrArg (fun m => m y)
        (laurentTerminalComponentMap_torus hπ data D j hj hk hp).symm⟩
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨l x, congrArg (fun m => m x)
        (laurentTerminalComponentMap_conic hπ data D j hj hk hp)⟩
    · exact ⟨r x, congrArg (fun m => m x)
        (laurentTerminalComponentMap_torus hπ data D j hj hk hp)⟩

end FLT.Mazur.WeierstrassDividedDepth
