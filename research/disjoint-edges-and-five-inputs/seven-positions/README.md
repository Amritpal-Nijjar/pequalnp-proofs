# Five-input circuit search for L-meta-18096

The target `0xfee8eaa8` is a monotone function on five inputs. A qualifying witness must contain a NOT reading a gate and use every non-output gate. The Lean filters imply exactly ten gates with a single internal NOT. They also allow a unary NOT and confine it to gates 2 through 8, numbering the ten gates from 1.

**Computational result.** The seven eligible positions have all been searched. No qualifying circuit was found. The two new placements were searched over 207,536 canonical five-gate prefixes. The earlier five placement records and sources are [pinned here](https://github.com/Amritpal-Nijjar/pequalnp-proofs/tree/694c3b11cae7c3b398821d768ea817e933719114/research/disjoint-edges-and-five-inputs/five-input-search).

| Location of NOT | Five-gate prefix classes | Eight-gate prefixes checked | Matching circuits |
|---|---:|---:|---:|
| Seventh gate | 207,536 | 21,367,906,560 | 0 |
| Eighth gate | 207,536 | 21,093,959,040 | 0 |

The early bank includes every signed-fresh monotone five-gate prefix up to permutations of the three symmetric inputs and reordering interchangeable wires. Its key records which wires are raw inputs, which are gate outputs, and which outputs still need a later use. Each candidate then runs through every possible wiring up to eight gates for the chosen NOT position. The last gate must use the penultimate output. Both final operations and every permitted other wire are checked on all 32 inputs. The printed quantities count loop indices for eight-gate prefixes, which include redundant choices. They are not counts of distinct ten-gate circuits.

Positive controls plant an actual live ten-gate circuit at each late placement. Another 136 eight-gate prefixes, including placements at root-bank boundaries, are checked individually against a simple host-language enumerator. The root records, their digests, and the resulting position totals are recorded in the archive.

## Independent CPU search

The separate native depth-first search completed 1,554 of 1,554 wiring partitions and reached 13,160,478,360 eight-gate prefixes in those finished partitions. All seven positions finished with zero witnesses.

| Gate number | CPU partitions completed | Eligible partitions | Eight-gate prefixes examined |
|---:|---:|---:|---:|
| 2 | 294 | 294 | 1,049,435,501 |
| 3 | 210 | 210 | 1,830,655,053 |
| 4 | 210 | 210 | 2,292,720,953 |
| 5 | 210 | 210 | 2,476,678,551 |
| 6 | 210 | 210 | 2,447,494,154 |
| 7 | 210 | 210 | 2,276,307,377 |
| 8 | 210 | 210 | 787,186,771 |

The CPU program constructs its own wirings sequentially. It uses the seven Lean-proved first-gate representatives. Its pruning uses signed freshness, limits on raw-input reads, restrictions obtained by fixing one input, and the number of earlier gates that still need a use. It does not share the GPU prefix canonicalization or the GPU finishing kernel. For the two strong four-input restrictions, `x0 = false` and `x4 = true`, at most two of the nine binary gates can become free. The bound is three for `x4 = false` and four for either value of each other restricted input. A collapsed restricted gate computes a constant or repeats an earlier wire up to complementation. The [checked Lean lemmas](https://github.com/Amritpal-Nijjar/pequalnp-proofs/tree/694c3b11cae7c3b398821d768ea817e933719114/research/disjoint-edges-and-five-inputs/five-input-lean) justify these filters for the posted question.

The CPU controls recovered 7 planted whole-circuit targets and compared the final-two-gate check against a direct search on 320 prefixes. These runs supply computation and reproducible coverage. The archive does not contain a Lean kernel proof that the complete desk statement is false.

## A Lean-verified way to reduce the input rows

Once the signal feeding the only NOT is fixed, split the 32 input rows by the value of that signal. For each group it suffices to test the minimal positive inputs and maximal negative inputs, ordered by inclusion of active switches. Inside a group the NOT has a fixed value, and the remaining AND/OR computation is monotone. The exact equivalence is proved for the project’s actual circuit evaluator in `proofs/MaskCircuit.lean`. It works for any number of inputs. The proof uses only Lean’s standard axioms.

For this target, a separate truth-table enumeration gives 14–25 required rows among the 5,255 monotone inverter-source functions incomparable with the target. This is a per-source count. The identity of the required rows depends on the source. Run `python round3_search/source_rows.py` for the distribution. The new [community comment](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19911299) describes a related extremal-input technique on another problem.

## Reproduction on Windows

Extract the archive. Use Python 3, a Windows OpenCL GPU driver, Clang and the LLVM linker. Run the commands from the `round3_search` directory. The root codes and banks can be reconstructed deterministically. Set a larger time budget to reproduce the complete CPU run on a slower processor.

```powershell
$end = [DateTimeOffset]::UtcNow.AddMinutes(60).ToString("o")
python roots.py --deadline $end
python sweep.py --deadline $end
clang -target x86_64-pc-windows-msvc -O3 -mpopcnt -ffreestanding -fno-builtin -fno-stack-protector -c native.c -o native.obj
lld-link /dll /noentry /nodefaultlib /out:native.dll native.obj
python native_run.py --deadline $end --workers 6
```

For the original data and outcomes, inspect the JSON files before replay. A replay writes fresh result JSONs in the extracted directory. [Posted statement](https://pequalnp.com/lemma#L-meta-18096) · [Project contribution instructions](https://pequalnp.com/join.txt)

To replay the separate input-row theorem, run `python proofs/replay_slice.py --project PATH_TO_PROJECT/lean --toolchain PATH_TO_LEAN_4.36.0`. Its earlier proof dependencies are included in the same directory.
