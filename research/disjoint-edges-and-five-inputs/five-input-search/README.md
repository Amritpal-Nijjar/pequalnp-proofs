# Five-input circuit search for L-meta-18096

The target is the five-input truth table `0xfee8eaa8`. The published Lean filters restrict a qualifying circuit to nine binary gates and one internal NOT. Every candidate must give the correct value on all 32 inputs and use every non-output gate. The seven possible NOT indices are 1 through 7 when counting from zero.

## Search by location of the NOT gate

| Zero-based index | Gate number | Prefix classes searched / generated | Qualifying hits |
|---:|---:|---:|---:|
| 1 | 2 | 3,376 / 3,376 | 0 |
| 2 | 3 | 7,054 / 7,054 | 0 |
| 3 | 4 | 6,584 / 6,584 | 0 |
| 4 | 5 | 139,964 / 139,964 | 0 |
| 5 | 6 | 2,884,684 / 2,884,684 | 0 |

Each completed class includes every remaining binary wiring, including both types of final gate. Prefix generation omits gates that would violate the established signed-freshness condition. Wire-bank equivalence uses the six input permutations that preserve the target. It also tracks which gate outputs still require a later use. The search permits the optional ignored second pin of a NOT when it changes this bookkeeping. Exact placement counts are computational findings. No Lean proof of these placement-wide exclusions was produced in this run.

## Checks and speed

Searching all replacements for the last five, six and seven gates of seven saved near-solutions produced zero qualifying circuits. A preliminary search without the use requirement found 122 matching intermediate states. Independent CPU expansion found that none could give a fully used circuit. All 21 planted positive examples were recovered across the three suffix lengths.

On the RTX 5080, the median for a 262,144-state benchmark was 0.227 ms including GPU readback versus 3.846 ms on one native CPU core (16.9×). Three byte-for-byte comparisons and 111 independent Python positive/negative controls passed. Benchmark timings apply to this kernel. Peak machine GPU utilization was 92% and peak physical RAM use was 28.2 GiB during the sampled window.

## Replay on Windows

Use Python 3, an OpenCL-capable GPU with its Windows driver, Clang and the LLVM linker. Extract the archive and run the following PowerShell commands in that directory. The time limit in the example applies to the whole replay. Set a later deadline if needed. Prefix bank files for the later positions are regenerated locally.

```powershell
clang -target x86_64-pc-windows-msvc -O3 -mpopcnt -ffreestanding -fno-builtin -fno-stack-protector -c cpu_library.c -o cpu_library.obj
lld-link /dll /noentry /nodefaultlib /out:cpu_library.dll cpu_library.obj
$end = [DateTimeOffset]::UtcNow.AddMinutes(60).ToString("o")
python run_search.py TenGateNeighbors.json replay_relaxed.json --deadline $end
python run_live.py TenGateNeighbors.json replay_live.json --relaxed replay_relaxed.json --deadline $end
python validate_prefix_merge.py
foreach ($i in 1,2,3) { python slot_one.py TenGateNeighbors.json "replay_slot_$i.json" --position $i --deadline $end }
```

For a later index, run `python wide_positions.py prepare . --position 4 --deadline $end` followed by `python wide_positions.py scan . --position 4 --deadline $end`. Use 5 for the next position. Save a separate copy of original result JSONs before replay if you want to compare them. The prefix metadata contains the SHA-256 of each reproducibly ordered bank.

For the sixth-gate run, `python late_banks.py . --front slot_5_results.json --deadline $end` batches up to 512 banks per GPU call and works from the opposite end of the same verified prefix bank. Its independent range combines with the forward range in the coverage table. Omitting `--front` replays the entire bank in reverse order.

In the recorded sixth-gate run a Windows file lock interrupted the forward checkpoint writer. The saved forward interval is [0, 543784). The reverse search finished [543784, 2884684) and verified the same prefix-bank digest. Together the two checkpoints cover the full bank. The bundled writer retries temporary locks during replay.

[Posted question](https://pequalnp.com/lemma#L-meta-18096) · [Seven NOT positions and Lean sources](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19910716)
