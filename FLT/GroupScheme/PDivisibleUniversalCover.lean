/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleSquareZeroColimitLift
public import FLT.GroupScheme.ShiftLimitEquivalence

/-! # Unique compatible lifts of inverse-p sequences across square-zero thickenings -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Inverse-p sequences in the actual original point colimit. -/
abbrev UniversalCover (B : Type) [CommRing B] [Algebra R B] :=
  ShiftLimit (X.pointColimitMul (B := B) p)

variable {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- A coefficient map acts on every point of a compatible sequence. -/
def universalCoverMap (q : B →ₐ[R] C) : X.UniversalCover B → X.UniversalCover C :=
  ShiftLimit.map (X.pointColimitMap q) (fun x ↦ (X.pointColimitMul_map p q x).symm)

/-- Formal etaleness of inverse-p sequences, proved by shifting the canonical lift. -/
def universalCoverSquareZeroEquiv (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (s : ℕ)
    (hs : ∀ b ∈ RingHom.ker q, p ^ s • b = 0) :
    X.UniversalCover B ≃ X.UniversalCover C :=
  ShiftLimit.equiv (X.pointColimitMap q) (fun x ↦ (X.pointColimitMul_map p q x).symm)
    (X.squareZeroColimitLift q hq hJ (p ^ s) hs) s
    (X.squareZeroColimitLift_mul q hq hJ (p ^ s) hs p)
    (fun x ↦ (X.squareZeroColimitLift_map q hq hJ (p ^ s) hs x).trans
      (X.pointColimitMul_iterate s x).symm)
    (fun x ↦ (X.squareZeroColimitLift_reduction q hq hJ (p ^ s) hs x).trans
      (X.pointColimitMul_iterate s x).symm)

/-- This equivalence is the actual reduction map on every coordinate. -/
theorem universalCoverSquareZeroEquiv_apply (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (s : ℕ)
    (hs : ∀ b ∈ RingHom.ker q, p ^ s • b = 0) (x : X.UniversalCover B) :
    X.universalCoverSquareZeroEquiv q hq hJ s hs x = X.universalCoverMap q x := rfl

/-- Every specified inverse-p sequence has exactly one compatible lift. -/
theorem existsUnique_universalCover_lift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (s : ℕ)
    (hs : ∀ b ∈ RingHom.ker q, p ^ s • b = 0) (x : X.UniversalCover C) :
    ∃! y : X.UniversalCover B, X.universalCoverMap q y = x :=
  (X.universalCoverSquareZeroEquiv q hq hJ s hs).bijective.existsUnique x

/-- Coefficient-map composition is retained on the entire compatible sequence. -/
theorem universalCoverMap_comp {D : Type} [CommRing D] [Algebra R D]
    (q : B →ₐ[R] C) (q' : C →ₐ[R] D) (x : X.UniversalCover B) :
    X.universalCoverMap (q'.comp q) x = X.universalCoverMap q' (X.universalCoverMap q x) := by
  apply Subtype.ext
  funext n
  exact X.pointColimitMap_comp q q' (x.val n)

end ThreeAdicPlan.PDivisibleSystem
