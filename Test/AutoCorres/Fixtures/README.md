# AutoCorres C fixtures

These files are byte-for-byte copies from
[`seL4/l4v@bc2599a59c43e673dca021b10b9841e9b8da4430`](https://github.com/seL4/l4v/tree/bc2599a59c43e673dca021b10b9841e9b8da4430).
They retain their upstream category-relative paths:

| Local category | Upstream path | Files |
| --- | --- | ---: |
| `examples/` | `tools/autocorres/tests/examples/*.c` and `alloc.h` | 26 (25 C, 1 header) |
| `parse-tests/` | `tools/autocorres/tests/parse-tests/*.c` | 21 |
| `proof-tests/` | `tools/autocorres/tests/proof-tests/*.c` | 16 |
| `doc/quickstart/` | `tools/autocorres/doc/quickstart/*.c` | 3 |
| `failing/` | `tools/autocorres/tests/failing/*.c` | 2 |
| **Total** | | **68 (67 C, 1 header)** |

The fixtures are copyright their upstream authors and distributed under the
BSD-2-Clause license identified by their upstream SPDX headers. No Isabelle
`.thy` files are included in this snapshot.
