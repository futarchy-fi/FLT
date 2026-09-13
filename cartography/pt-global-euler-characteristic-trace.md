# Global Euler--Poincare characteristic: full dependency trace

Closure artifact for **PT-R1** (bead `hub-lsb1u.7.5`).  This discharges the
dependency-honesty panel's objection to node 12 of `pt-reconciled.md`: the node
had a theorem number but no proof-level predecessor trace.

Primary source: J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I,
Theorem 5.1 and pp. 67--71 (PDF pp. 73--78).  The trace below follows Milne's
proof rather than inferring prerequisites from the displayed formula.

## Frozen statement

Let `K` be a global field, `S` a finite nonempty set of places containing every
archimedean place, and `M` a finite `G_S`-module whose order is a unit in the
ring of `S`-integers.  Write

```text
chi(G_S,M) = #H^0(G_S,M) * #H^2(G_S,M) / #H^1(G_S,M).
```

Then

```text
chi(G_S,M) = product_{v archimedean} #H^0(G_v,M) / |#M|_v.
```

For number fields this is the exact finite-module statement needed upstream of
Greenberg--Wiles.  Real-place periodicity is why this is a truncated
`H^0,H^1,H^2` characteristic, not an unrestricted alternating product.

## Dependency trace

| Edge | Input used in Milne's proof | Exact role | Ownership |
|---|---|---|---|
| EC1 | Global cohomology `H^r(G_S,M)` and long exact sequences | Defines the three finite orders and proves multiplicativity in short exact sequences (Lemma 5.3) | PT nodes 1, 3 |
| EC2 | Global finiteness, Milne I.4.15 | Makes `#H^r(G_S,M)` meaningful | PT node 3 |
| EC3 | Global duality/Poitou--Tate complex, Milne I.4.10 | Exactness gives `chi(G_S,M) chi(G_S,M^D) = product_{v in S} chi(K_v,M)` and controls high degrees at real places | **PT node 11 in full**, plus CFT exports 6/D2; node 11' is insufficient |
| EC4 | Local Euler characteristic, Milne I.2.8 | Replaces each nonarchimedean local factor by the normalized module order `|#M|_v` | PT node 8 |
| EC5 | Archimedean Tate cohomology and duality, Milne I.2.13 | Rewrites the real/complex factors and handles periodic cohomology | PT nodes 5, 7, 9 |
| EC6 | Product formula for the normalized absolute values of the integer `#M` | Cancels all nonarchimedean factors outside the displayed archimedean product | **CFT/arithmetic boundary input; not supplied by bare local invariant maps** |
| EC7 | Additivity of the defect `phi(M)` (Milne Lemma 5.3) | Reduces the theorem through composition factors to modules killed by one prime | PT local algebra |
| EC8 | A finite Galois splitting field containing the needed roots of unity; restriction/induction and Grothendieck groups of finite-field representations | Reduces to a cyclic group of order prime to `p`, as in the proof of local Theorem I.2.8 | CFT/Galois substrate plus PT cohomology |
| EC9 | Cup product/evaluation and exactness of `Hom(-,F_p)` (Milne Lemma 5.4) | Identifies the cohomological virtual classes of `M` and `M^D`, proving `phi(M)=phi(M^D)` | PT node 2 plus finite-group cohomology |
| EC10 | Herbrand quotient one and periodicity for finite cyclic groups | Cancels the remaining real-place/high-degree correction terms | PT nodes 5, 9 |

The proof flow is therefore:

```text
global finiteness + definition
  -> duality exactness relates M and M^D to all local factors
  -> local Euler characteristic + product formula leave archimedean factors
  -> defect multiplicativity reduces to p-torsion modules
  -> splitting-field/cyclic reduction + cup product prove defect(M)=defect(M^D)
  -> duality already gave defect(M) defect(M^D)=1
  -> defect(M)=1.
```

## Boundary and sizing verdict

The panel's suspected leak is real and changes the closure graph: node 12 does
**not** follow from middle-exactness 11' or from the local invariant and
sum-of-invariants exports alone.  Milne proves it using the full global-duality
complex I.4.10, so node 11 remains a proof predecessor even though the
consumer-facing Greenberg--Wiles interface can stay descoped to 11'.  The proof
also uses the normalized global product formula and a
splitting-field/restriction package.  Those inputs must be named
CFT/arithmetic predecessors.  It does not require class-group finiteness or the
unit theorem in Milne's proof.

Keep the node at **L locally / XL closure**.  The finite-group representation and
cup-product part is reusable and comparatively contained; the closure inherits
global duality, local Euler characteristic, restricted-product conventions and
the CFT boundary exports.  Greenberg--Wiles may consume Theorem 5.1 as a theorem
interface, but proving it is not an isolated L-sized leaf.

## Sources

- Milne, *Arithmetic Duality Theorems*, 2nd ed., I.5.1, pp. 67--71:
  https://math.stanford.edu/~conrad/BSDseminar/refs/MilneADT.pdf
- Milne's official book page:
  https://www.jmilne.org/math/Books/adt.html
