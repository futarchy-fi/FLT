/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedTateAcyclic

/-!
# Coinduced acyclicity on every subgroup

Coset coordinates identify restricted functions on the group with coinduced
functions on a subgroup. This proves cohomological triviality on all subgroups,
not just vanishing for the ambient group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G) (H : Subgroup G)

/-- Coordinates given by a chosen coset representative and a subgroup element. -/
def subgroupCosetCoordinates : (G ⧸ H) × H ≃ G where
  toFun p := p.1.out * p.2
  invFun g := ⟨QuotientGroup.mk g, ⟨(QuotientGroup.mk g : G ⧸ H).out⁻¹ * g,
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g))⟩⟩
  left_inv p := by
    rcases p with ⟨q, h⟩
    have hq : (QuotientGroup.mk (q.out * h) : G ⧸ H) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ h.property, QuotientGroup.out_eq']
    simp only [hq]
    congr 1
    apply Subtype.ext
    simp
  right_inv _ := by simp

/-- Coset coordinates intertwine subgroup translation with right translation. -/
def coinducedSubgroupIso : Rep.res H.subtype (coinducedCoefficients M) ≅
    coinducedCoefficients (Rep.trivial k H ((G ⧸ H) → M)) :=
  Rep.mkIso (.mk {
    toFun f h q := f (subgroupCosetCoordinates H (q, h))
    invFun f g := f ((subgroupCosetCoordinates H).symm g).2
      ((subgroupCosetCoordinates H).symm g).1
    left_inv f := by funext g; simp
    right_inv f := by funext h q; simp
    map_add' _ _ := rfl
    map_smul' _ _ := rfl } (fun g => by
      ext f h q
      change f ((q.out * h) * g) = f (q.out * (h * g))
      rw [mul_assoc]))

/-- The concrete coefficient module is Tate acyclic after restriction to every finite subgroup. -/
theorem coinducedSubgroupTate_isZero [Fintype H] (n : ℤ) :
    Limits.IsZero (tateCohomology (Rep.res H.subtype (coinducedCoefficients M)) n) :=
  (coinducedTate_isZero (Rep.trivial k H ((G ⧸ H) → M)) n).of_iso
    ((tateCohomologyFunctor n).mapIso (coinducedSubgroupIso M H))

end LocalClassFieldTheory
