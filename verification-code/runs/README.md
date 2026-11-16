# runs/ — outputs of computations

Organised into subdirectories on 2026-11-08 (Jan's rule of thumb: several runs of one series
go in a subdirectory; a single run may stay here). The files were moved with
`92-code/move_tracked.py`, which rewrote the links in `.md` and `.org` files. The scripts that
write here had their paths updated by hand in the same commit. The code that produced a file
is usually in `code/oneoff/`; the pipelines are in `code/`.

- **`face-lattice/`** — Sage face-lattice statistics of rasimp(a) + shift^d rasimp(a), for a the
  all-ones or the Kozlov vector, 2026-07 and 08. Its `README.md` was `runs/description.md`.
  Produced by `code/face_lattice_pipeline.py`, `code/pipeline_orchestrator.py` and
  `code/face_lattice_stats.py`; LOGBOOK sessions 03–04.
- **`paramspace/`** — parameter-space experiments, n = 4 and 5 with d = 1, 2026-07-31 and 08-01.
  Produced by `code/oneoff/parameter_space_*`; LOGBOOK sessions 03–04.
- **`ffp-asymptotics/`** — the asymptotics-in-p checks (improper and proper), their
  re-verifications of 2026-09-16 and the reruns of 2026-10-08. Produced by
  `code/oneoff/ffp_*asymptotics_in_p_check.py`; LOGBOOK sessions 27–28 and 46.
- **`lean-anchors/`** — where each numbered statement sits in the Lean library, 2026-09-17/18;
  LOGBOOK sessions 33–37.
- **`2026-10-08_article2-reverification/`** — the Part II re-verification batch before
  submission (`code/linusson_ff_counting.py`, `code/oneoff/appendix_tables*.py` and others);
  LOGBOOK session 46.
- **`2026-10-20_article3-overnight-push/`** — the Part III overnight push: checks, agent reviews
  and referee runs (`code/oneoff/*review*`, `referee_article3_checks*`,
  `kozlov_volume_ehrhart.py` and others); LOGBOOK session 53. **It also holds the logs of Parts
  IV and V**, which were split out of Part III after this run (2026-11-07 and 11-09): for IV,
  `pairwise-gap-gluing-*`, `kozlov-pairwise-hside-check*`, `kozlov_hdesc_verify`,
  `allones_hdesc_verify`, `review-hdesc`, `review-pairwise-*`; for V, `greedy_optimality` and
  `review-module-kk`. The name is kept because scripts read from it.
- **`2026-11-16_part5-checks/`** — the two Part V scripts that had no recorded run until then:
  `code/oneoff/lean_check_module_kk.py` (lex shadows, rank-one Kruskal–Katona and the greedy
  split against brute force, the statements formalised in `ModuleKK/`; 0 bad in all three) and
  `code/oneoff/ff_koz_intersection_check.sage` (FF(n;d) ∩ Koz(n;d) = FF_pr(n;d), Part V's open
  problem 2; 68 cases, 0 failures). Run on jts-office, Python 3.14.7 and SageMath 10.9; LOGBOOK
  session 58.
- **`fibres/`** — fibre counts of the sum map, from 2026-11-08, with its own README
  (`code/fibres/`, `code/oneoff/small_n_fibre_counts.py`); LOGBOOK session 56 onwards.

The files left at this level are single runs; each one's header, or the LOGBOOK entry of its
date, says what produced it.
