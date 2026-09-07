# Comparator for `pure_wz2_theorem5_2_unconditional`

The trusted challenge statement is self-contained over Mathlib. It does not
import any file under `MyLeanRepo`. The definitions used by the theorem are
split into the following audit layers:

1. `Statements/JohnEllipsoid.lean`: outer John ellipsoid interface.
2. `Statements/AssertionD.lean`: ordinary tubes and `realRpowENN`.
3. `Statements/Geometry.lean`: streamlined bodies.
4. `Statements/Families.lean`: indexed families and shadings.
5. `Statements/Definition2_12.lean`: the literal nearby-scale CWA predicate.
6. `Statements/Core.lean`: the paper-facing Theorem 5.2 proposition.

`Statements/JohnEllipsoid.lean` contains the one trusted theorem hole
`exists_isOuterJohnEllipsoid`. It is listed in `theorem_names`, so Comparator
checks that the repository proves exactly the same theorem and that its proof
uses only the permitted axioms. The target theorem is checked in the same way.

The root files retain the exact Mathlib import sets used by their canonical
repository sources. `#min_imports` confirmed that every later statement layer
only needs the immediately preceding trusted layers. This avoids the unrelated
instances introduced by a blanket `import Mathlib`, while keeping every
statement dependency locally auditable.

Use Comparator and lean4export builds matching Lean `v4.32.0-rc1`, then run
from the repository root:

```sh
COMPARATOR_LANDRUN=/path/to/landrun \
COMPARATOR_LEAN4EXPORT=/path/to/lean4export \
lake env /path/to/comparator Comparator/config.json
```

The successful result ends with:

```text
Lean default kernel accepts the solution
Your solution is okay!
```
