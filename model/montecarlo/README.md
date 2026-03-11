# Random sampling models

Models used to predict the influence of distributed consensus protocol parameters on its performance.

The Monte-Carlo CLI supports single-run mode (default, `--runs<=1`) with per-snapshot reports,
and parallel batch mode (`--runs>1`) that executes independent runs in a worker pool and reports
aggregate convergence statistics (`min/mean/median/max`) over successful runs.
