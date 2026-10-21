/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentIntersection
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer
public import FLT.Mazur.SchemeOpenChartRange

/-!
# Adjacent boundary transfer on actual arithmetic pair domains

At every quotient order, change the first input to the next retained chart
on the full incidence-open domain of its relative product with any second
input. The actual resolved arithmetic inputs, and hence their contractions,
are unchanged. The transferred first abscissa is nonzero throughout.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "eNext" => data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) 2
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) Q 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "B" => PrincipalOpenTensor.transitionIso Q x u (previousBoundaryEquiv hπ e eNext)
local notation "a" => (A).inv ≫ PrincipalOpenTensor.inclusion Q t
local notation "b" => (B).inv ≫ PrincipalOpenTensor.inclusion Q u
local notation "old" => finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr
local notation "next" => finiteArithmeticOlderTensorChart hπ data m (j + 1) hjNext r hr
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 2 + r) hr m
local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "H" => adjacentArithmeticTensor_isPullback hπ data m j hj hjNext r hr
variable {Y : Scheme}
  (g : Y ⟶ Spec (.of (PolygonArithmeticStages.Quotient R π m)))

/-- The whole incidence-open domain in the original older arithmetic relative pair. -/
def arithmeticAdjacentPairOpen : (pullback f g).Opens :=
  SchemePairBoundaryTransfer.domain f g a

local notation "O" => arithmeticAdjacentPairOpen hπ data m j hj r hr g

/-- The pair domain is exactly the nonvanishing locus of the first incidence coordinate. -/
theorem arithmeticAdjacentPairOpen_mem (p : (pullback f g : Scheme)) :
    p ∈ O ↔ tt ∉ (pullback.fst f g p).asIdeal := by
  change pullback.fst f g p ∈ Set.range a ↔ _
  have he := SchemeOpenChartRange.range_iso_comp (A).symm
    (PrincipalOpenTensor.inclusion Q t)
  exact (congrArg (fun U => pullback.fst f g p ∈ U) he).to_iff.trans
    (PrincipalOpenTensor.mem_inclusion_range Q t _)

/-- The original common boundary gives a scheme map to the next arithmetic pair. -/
def arithmeticAdjacentPairTransfer : (O).toScheme ⟶ pullback f' g :=
  SchemePairBoundaryTransfer.transfer f f' g a b (by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ s) (H).w)

local notation "transfer" => arithmeticAdjacentPairTransfer hπ data m j hj hjNext r hr g

/-- Both actual first inputs agree in the resolved arithmetic stage. -/
@[reassoc] theorem arithmeticAdjacentPairTransfer_first :
    transfer ≫ pullback.fst f' g ≫ next = (O).ι ≫ pullback.fst f g ≫ old :=
  SchemePairBoundaryTransfer.transfer_first_ambient f f' g a b _ old next (H).w

/-- The second input retains its entire original morphism. -/
@[reassoc] theorem arithmeticAdjacentPairTransfer_second :
    transfer ≫ pullback.snd f' g = (O).ι ≫ pullback.snd f g :=
  SchemePairBoundaryTransfer.transfer_snd f f' g a b _

/-- The new coordinates stay in the full horizontal puncture on the whole pair domain. -/
theorem arithmeticAdjacentPairTransfer_punctured (p : (O).toScheme) :
    tu ∉ (pullback.fst f' g (transfer p)).asIdeal := by
  have he := congrArg (fun k => k p)
    (SchemePairBoundaryTransfer.transfer_fst f f' g a b (by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ s) (H).w))
  change pullback.fst f' g (transfer p) = b _ at he
  rw [he]
  exact (PrincipalOpenTensor.mem_inclusion_range Q u _).mp ⟨_, rfl⟩

/-- Any subsequent contraction of the actual first input is preserved as a whole morphism. -/
@[reassoc] theorem arithmeticAdjacentPairTransfer_contraction {Z : Scheme}
    (c : finiteGlobalArithmeticStage hπ data (j + 2 + r) hr m ⟶ Z) :
    transfer ≫ pullback.fst f' g ≫ next ≫ c =
      (O).ι ≫ pullback.fst f g ≫ old ≫ c := by
  rw [arithmeticAdjacentPairTransfer_first_assoc]

end FLT.Mazur.WeierstrassDividedDepth
